(* 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF never halts. *)

From Coq Require Import Bool List Lists.Streams PeanoNat Lia String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF".
Arguments tm _ : simpl never.

Module Internal.

Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Notation "'0inf'" := (@const Sym S0).

(* ========================================================================== *)
(* Section 1: Tape & Stream Helpers, Fast Execution Tactics                   *)
(* ========================================================================== *)

Lemma ptrans {c1 c2 c3 : Q * tape} :
  c1 -[ tm ]->+ c2 -> c2 -[ tm ]->+ c3 -> c1 -[ tm ]->+ c3.
Proof. apply progress_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} :
  c1 -[ tm ]->* c2 -> c2 -[ tm ]->+ c3 -> c1 -[ tm ]->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma zero_cons_0inf : S0 >> 0inf = 0inf.
Proof. symmetry. apply const_unfold. Qed.

Lemma lpow_S_sym (x : Sym) (n : nat) :
  [x] ^^ (n + 1) = x :: ([x] ^^ n).
Proof.
  replace (n + 1) with (S n) by lia.
  reflexivity.
Qed.

Lemma lpow_app_one (x : Sym) (n : nat) :
  [x] ^^ n ++ [x] = [x] ^^ (n + 1).
Proof.
  rewrite lpow_shift.
  rewrite lpow_S_sym.
  reflexivity.
Qed.

Lemma side_pow_add (s : side) (n m : nat) :
  [S1] ^^ n *> ([S1] ^^ m *> s) = [S1] ^^ (n + m) *> s.
Proof.
  apply lpow_add'.
Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl';
   cbn [Streams.hd Streams.tl];
   (reflexivity || (repeat rewrite <- const_unfold; reflexivity)))
  || finish_progress.

Ltac run_steps :=
  cbn [Str_app Streams.hd Streams.tl];
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  repeat (try solve [fast_finish]; fast_step).

(* ========================================================================== *)
(* Section 2: Step-Indexed Safety                                             *)
(* ========================================================================== *)

Definition Safe (k : nat) (c : Q * tape) : Prop :=
  forall j, j <= k -> ~ halts_in tm c j.

Lemma Safe_of_stepPlus {k : nat} {c c' : Q * tape}
    (Hstep : c -[ tm ]->+ c')
    (Hsafe : forall k', k' < k -> Safe k' c') :
  Safe k c.
Proof.
  intros j Hj Hhalt.
  destruct (progress_multistep _ _ _ Hstep) as [n Hms].
  destruct (Nat.leb_spec (S n) j) as [Hle | Hlt].
  - assert (Hlt_k : j - S n < k) by lia.
    apply (Hsafe (j - S n) Hlt_k (j - S n) (Nat.le_refl _)).
    exact (preceeds_halt _ _ _ _ _ Hhalt Hms Hle).
  - assert (Hgt : S n > j) by lia.
    exact (exceeds_halt _ _ _ _ _ Hhalt Hgt Hms).
Qed.

Lemma nonhalt_of_forall_safe (c_start : Q * tape)
    (Hinit : c0 -[ tm ]->+ c_start)
    (Hsafe : forall k, Safe k c_start) :
  ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact (progress_evstep _ _ _ Hinit).
  - intros [k Hhalt].
    exact (Hsafe k k (Nat.le_refl k) Hhalt).
Qed.

(* ========================================================================== *)
(* Section 3: Unary-Bitstring Left Encoding & Right-Tape Buffer Encoding      *)
(* ========================================================================== *)

Fixpoint encBits (w : list bool) : side :=
  match w with
  | [] => 0inf
  | false :: w' => S1 >> encBits w'
  | true  :: w' => S1 >> S0 >> encBits w'
  end.

Fixpoint zeros (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => false :: zeros n'
  end.

Fixpoint ones (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => true :: ones n'
  end.

Lemma zeros_add (a b : nat) : zeros (a + b) = zeros a ++ zeros b.
Proof.
  induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add zeros List.app]. rewrite IH. reflexivity.
Qed.

Lemma encBits_zeros (d : nat) (w : list bool) :
  encBits (zeros d ++ w) = [S1] ^^ d *> encBits w.
Proof.
  induction d as [| d IH]; [reflexivity |].
  cbn [zeros List.app encBits lpow Str_app].
  rewrite IH. reflexivity.
Qed.

Lemma encBits_zeros_true (d : nat) (w : list bool) :
  encBits (zeros d ++ true :: w) =
    [S1] ^^ (d + 1) *> (S0 >> encBits w).
Proof.
  rewrite encBits_zeros. cbn [encBits].
  change (S1 >> S0 >> encBits w) with ([S1] ^^ 1 *> (S0 >> encBits w)).
  rewrite side_pow_add. reflexivity.
Qed.

Lemma encBits_nonempty_head (w : list bool) (hw : w <> []) :
  exists t : side, encBits w = S1 >> t.
Proof.
  destruct w as [| [] w'].
  - contradiction.
  - exists (S0 >> encBits w'). reflexivity.
  - exists (encBits w'). reflexivity.
Qed.

Fixpoint encBuf (M : list nat) (s : side) : side :=
  match M with
  | [] => s
  | d :: M' => [S1] ^^ (d + 1) *> (S0 >> encBuf M' s)
  end.

Lemma one_cons_encBuf (d : nat) (M : list nat) (s : side) :
  S1 >> encBuf (d :: M) s = encBuf ((d + 1) :: M) s.
Proof.
  cbn [encBuf].
  replace (d + 1 + 1) with (S (d + 1)) by lia.
  reflexivity.
Qed.

Lemma one_0inf_eq_encBuf :
  S1 >> 0inf = encBuf [0] (S0 >> 0inf).
Proof.
  cbn [encBuf Nat.add lpow List.app Str_app].
  repeat rewrite zero_cons_0inf. reflexivity.
Qed.

Fixpoint sweepBits (M : list nat) (w : list bool) : list bool :=
  match M with
  | [] => w
  | d :: M' => sweepBits M' (zeros d ++ true :: w)
  end.

Lemma ones_app_true (r : nat) (w : list bool) :
  ones r ++ true :: w = true :: (ones r ++ w).
Proof.
  induction r as [| r IH]; [reflexivity |].
  cbn [ones List.app]. rewrite IH. reflexivity.
Qed.

Lemma sweepBits_zeros_rep (r : nat) (M : list nat) (w : list bool) :
  sweepBits (repeat 0 r ++ M) w = sweepBits M (ones r ++ w).
Proof.
  revert w.
  induction r as [| r IH]; intros w; [reflexivity |].
  cbn [repeat List.app sweepBits zeros].
  rewrite IH, ones_app_true. reflexivity.
Qed.

(* ========================================================================== *)
(* Section 4: Raw TM Sweep & Primitive C/B Step Rules                         *)
(* ========================================================================== *)

Lemma shift_F_1 (k : nat) (l r : side) :
  F;; l {{S1}} ([S1] ^^ k *> r) -[ tm ]->*
  F;; ([S1] ^^ k *> l) {{S1}} r.
Proof.
  revert l r.
  induction k as [| k IH]; intros l r.
  - apply evstep_refl.
  - cbn [lpow List.app Str_app].
    eapply evstep_trans.
    + apply progress_evstep. run_steps.
    + rewrite <- lpow_shift1.
      exact (IH (S1 >> l) r).
Qed.

Lemma shift_F_block (k : nat) (l s : side) :
  F;; l {{S1}} ([S1] ^^ k *> (S0 >> s)) -[ tm ]->+
  F;; ([S1] ^^ (k + 1) *> l) {{S0}} s.
Proof.
  eapply sp_trans; [exact (shift_F_1 k l (S0 >> s)) |].
  replace (k + 1) with (S k) by lia.
  cbn [lpow List.app Str_app].
  run_steps.
Qed.

Lemma f_step_block_raw (t : side) (d : nat) (s : side) :
  F;; (S1 >> t) {{S0}} ([S1] ^^ (d + 1) *> (S0 >> s)) -[ tm ]->+
  F;; ([S1] ^^ (d + 1) *> (S0 >> S1 >> t)) {{S0}} s.
Proof.
  eapply ptrans; [| exact (shift_F_block d (S0 >> S1 >> t) s)].
  rewrite lpow_S_sym. cbn [Str_app].
  run_steps.
Qed.

Lemma f_sweep_bits (M : list nat) (w : list bool) (hw : w <> []) (u : side) :
  F;; encBits w {{S0}} encBuf M (S0 >> u) -[ tm ]->+
  B;; encBits (sweepBits M w) {{S0}} (S1 >> u).
Proof.
  revert w hw.
  induction M as [| d M IH]; intros w hw.
  - destruct (encBits_nonempty_head w hw) as [t ht].
    cbn [encBuf sweepBits]. rewrite ht.
    run_steps.
  - destruct (encBits_nonempty_head w hw) as [t ht].
    eapply ptrans.
    + cbn [encBuf]. rewrite ht.
      exact (f_step_block_raw t d (encBuf M (S0 >> u))).
    + rewrite <- ht, <- encBits_zeros_true.
      apply IH. destruct d; discriminate.
Qed.

Definition cfgC (w : list bool) (M : list nat) (u : side) : Q * tape :=
  C;; encBits w {{S0}} (S0 >> encBuf M (S0 >> u)).

Definition cfgB (w : list bool) (d : nat) (M : list nat) (u : side) : Q * tape :=
  B;; encBits w {{S0}} (S1 >> encBuf (d :: M) (S0 >> u)).

Definition retB (w : list bool) (u : side) : Q * tape :=
  B;; encBits w {{S0}} (S1 >> u).

Lemma step_C_ff (w : list bool) (hw : w <> []) (M : list nat) (u : side) :
  cfgC (false :: false :: w) M u -[ tm ]->+
  retB (sweepBits M (false :: true :: w)) u.
Proof.
  destruct (encBits_nonempty_head w hw) as [t ht].
  eapply ptrans.
  - unfold cfgC. cbn [encBits]. rewrite ht.
    instantiate (1 := F;; encBits (false :: true :: w) {{S0}} encBuf M (S0 >> u)).
    cbn [encBits]. rewrite ht. run_steps.
  - exact (f_sweep_bits M (false :: true :: w) ltac:(discriminate) u).
Qed.

Lemma step_C_ft (w : list bool) (M : list nat) (u : side) :
  cfgC (false :: true :: w) M u -[ tm ]->+ cfgB w 1 M u.
Proof.
  unfold cfgC, cfgB. cbn [encBits encBuf Nat.add lpow List.app Str_app].
  run_steps.
Qed.

Lemma step_C_t (w : list bool) (M : list nat) (u : side) :
  cfgC (true :: w) M u -[ tm ]->+ cfgC w (0 :: M) u.
Proof.
  unfold cfgC. cbn [encBits encBuf Nat.add lpow List.app Str_app].
  run_steps.
Qed.

Lemma step_C_ones_ff (r : nat) (w : list bool) (hw : w <> [])
    (M : list nat) (u : side) :
  cfgC (ones r ++ false :: false :: w) M u -[ tm ]->+
  retB (sweepBits M (ones r ++ false :: true :: w)) u.
Proof.
  revert M.
  induction r as [| r IH]; intros M.
  - exact (step_C_ff w hw M u).
  - eapply ptrans; [exact (step_C_t (ones r ++ false :: false :: w) M u) |].
    pose proof (IH (0 :: M)) as H.
    cbn [sweepBits zeros List.app] in H. exact H.
Qed.

Lemma repeat_0_cons (r : nat) (M : list nat) :
  repeat 0 r ++ 0 :: M = repeat 0 (S r) ++ M.
Proof.
  induction r as [| r IH]; [reflexivity |].
  change (repeat 0 (S r)) with (0 :: repeat 0 r).
  change (repeat 0 (S (S r))) with (0 :: repeat 0 (S r)).
  cbn [List.app]. rewrite IH. reflexivity.
Qed.

Lemma step_C_ones_ft (r : nat) (w : list bool) (M : list nat) (u : side) :
  cfgC (ones r ++ false :: true :: w) M u -[ tm ]->+
  cfgB w 1 (repeat 0 r ++ M) u.
Proof.
  revert M.
  induction r as [| r IH]; intros M.
  - exact (step_C_ft w M u).
  - eapply ptrans; [exact (step_C_t (ones r ++ false :: true :: w) M u) |].
    pose proof (IH (0 :: M)) as H.
    rewrite repeat_0_cons in H. exact H.
Qed.

Lemma step_B_nil (d : nat) (M : list nat) (u : side) :
  cfgB [] d M u -[ tm ]->+
  retB (sweepBits M (zeros (d + 1) ++ [false; false; false; false; true])) u.
Proof.
  unfold cfgB. cbn [encBits encBuf].
  eapply ptrans.
  - eapply ptrans;
      [| exact (shift_F_block (2 + (d + 1)) ([S1] ^^ 2 *> 0inf) (encBuf M (S0 >> u)))].
    rewrite <- (side_pow_add _ 2 (d + 1)).
    cbn [lpow List.app Str_app].
    run_steps.
  - rewrite side_pow_add.
    replace (2 + (d + 1) + 1 + 2) with (d + 5 + 1) by lia.
    replace (F;; ([S1] ^^ (d + 5 + 1) *> 0inf) {{S0}} encBuf M (S0 >> u))
      with (F;; encBits (zeros (d + 5) ++ [true]) {{S0}} encBuf M (S0 >> u)).
    + replace (zeros (d + 1) ++ [false; false; false; false; true])
        with (zeros (d + 5) ++ [true]).
      * apply f_sweep_bits. destruct d; discriminate.
      * replace (d + 5) with ((d + 1) + 4) by lia.
        rewrite zeros_add, <- app_assoc. reflexivity.
    + rewrite encBits_zeros_true. cbn [encBits].
      rewrite zero_cons_0inf. reflexivity.
Qed.

Lemma step_B_true_nil (d : nat) (M : list nat) (u : side) :
  cfgB [true] d M u -[ tm ]->+
  retB (sweepBits M (zeros (d + 1) ++ [false; false; false; false; true])) u.
Proof.
  unfold cfgB. cbn [encBits encBuf].
  eapply ptrans.
  - eapply ptrans;
      [| exact (shift_F_block (2 + (d + 1)) ([S1] ^^ 2 *> 0inf) (encBuf M (S0 >> u)))].
    rewrite <- (side_pow_add _ 2 (d + 1)).
    cbn [lpow List.app Str_app].
    run_steps.
  - rewrite side_pow_add.
    replace (2 + (d + 1) + 1 + 2) with (d + 5 + 1) by lia.
    replace (F;; ([S1] ^^ (d + 5 + 1) *> 0inf) {{S0}} encBuf M (S0 >> u))
      with (F;; encBits (zeros (d + 5) ++ [true]) {{S0}} encBuf M (S0 >> u)).
    + replace (zeros (d + 1) ++ [false; false; false; false; true])
        with (zeros (d + 5) ++ [true]).
      * apply f_sweep_bits. destruct d; discriminate.
      * replace (d + 5) with ((d + 1) + 4) by lia.
        rewrite zeros_add, <- app_assoc. reflexivity.
    + rewrite encBits_zeros_true. cbn [encBits].
      rewrite zero_cons_0inf. reflexivity.
Qed.

Lemma step_B_ff (w : list bool) (hw : w <> []) (d : nat) (M : list nat) (u : side) :
  cfgB (false :: false :: w) d M u -[ tm ]->+
  retB (sweepBits M (zeros (d + 1) ++ true :: true :: w)) u.
Proof.
  destruct (encBits_nonempty_head w hw) as [t ht].
  eapply ptrans; [| exact (f_sweep_bits (0 :: (d + 1) :: M) w hw u)].
  unfold cfgB. cbn [encBits encBuf]. rewrite ht.
  replace (0 + 1) with 1 by lia.
  replace (d + 1 + 1) with (S (d + 1)) by lia.
  cbn [lpow List.app Str_app].
  run_steps.
Qed.

Lemma step_B_ft (w : list bool) (d : nat) (M : list nat) (u : side) :
  cfgB (false :: true :: w) d M u -[ tm ]->+ cfgB w 0 ((d + 1) :: M) u.
Proof.
  unfold cfgB. cbn [encBits encBuf].
  replace (0 + 1) with 1 by lia.
  replace (d + 1 + 1) with (S (d + 1)) by lia.
  cbn [lpow List.app Str_app].
  run_steps.
Qed.

Lemma step_B_t (w : list bool) (d : nat) (M : list nat) (u : side) :
  cfgB (true :: w) d M u -[ tm ]->+
  cfgC w [] (S1 >> encBuf (d :: M) (S0 >> u)).
Proof.
  unfold cfgB, cfgC. cbn [encBits encBuf].
  run_steps.
Qed.

Lemma retB_of_B_t (w : list bool) (d : nat) (M : list nat) (u : side) :
  retB w (S1 >> encBuf (d :: M) (S0 >> u)) = cfgB w (d + 1) M u.
Proof.
  unfold retB, cfgB. rewrite one_cons_encBuf. reflexivity.
Qed.

Lemma step_B_ones_ff (r : nat) (w : list bool) (hw : w <> [])
    (d : nat) (M : list nat) (u : side) :
  cfgB (true :: (ones r ++ false :: false :: w)) d M u -[ tm ]->+
  cfgB (ones r ++ false :: true :: w) (d + 1) M u.
Proof.
  eapply ptrans; [exact (step_B_t (ones r ++ false :: false :: w) d M u) |].
  pose proof (step_C_ones_ff r w hw [] (S1 >> encBuf (d :: M) (S0 >> u))) as H.
  cbn [sweepBits] in H. rewrite retB_of_B_t in H. exact H.
Qed.

Lemma step_B_ones_ft (r : nat) (w : list bool) (d : nat) (M : list nat) (u : side) :
  cfgB (true :: (ones r ++ false :: true :: w)) d M u -[ tm ]->+
  cfgB w 1 (repeat 0 r) (S1 >> encBuf (d :: M) (S0 >> u)).
Proof.
  eapply ptrans; [exact (step_B_t (ones r ++ false :: true :: w) d M u) |].
  pose proof (step_C_ones_ft r w [] (S1 >> encBuf (d :: M) (S0 >> u))) as H.
  rewrite app_nil_r in H. exact H.
Qed.

Lemma step_top_ff (w : list bool) (hw : w <> []) :
  retB (false :: false :: w) 0inf -[ tm ]->+ retB (true :: true :: w) 0inf.
Proof.
  destruct (encBits_nonempty_head w hw) as [t ht].
  eapply ptrans.
  - unfold retB. cbn [encBits]. rewrite ht.
    instantiate (1 := F;; encBits w {{S0}} encBuf [0; 0] (S0 >> 0inf)).
    cbn [encBuf Nat.add lpow List.app Str_app].
    rewrite ht, zero_cons_0inf. run_steps.
  - exact (f_sweep_bits [0; 0] w hw 0inf).
Qed.

Lemma step_top_t (w : list bool) :
  retB (true :: w) 0inf -[ tm ]->+ cfgC w [] (S1 >> 0inf).
Proof.
  unfold retB, cfgC. cbn [encBits encBuf].
  run_steps.
Qed.

Lemma retB_of_top_t (w : list bool) :
  retB w (S1 >> 0inf) = cfgB w 0 [] 0inf.
Proof.
  unfold retB, cfgB. rewrite one_0inf_eq_encBuf. reflexivity.
Qed.

Lemma init_reaches_start :
  c0 -[ tm ]->+ retB [false; false; false; true] 0inf.
Proof.
  unfold c0, tape0, retB. cbn [encBits].
  run_steps.
Qed.

(* ========================================================================== *)
(* Section 5: The 10-State Mealy Pair-DFA Q10                                 *)
(* ========================================================================== *)

Inductive Q10 : Type :=
  | qS0 | qS1 | qSd
  | qD0 | qD1 | qD2
  | qZ0a | qZ0b | qZ1a | qZ1b.

Fixpoint InL (q : Q10) (w : list bool) : Prop :=
  match q, w with
  | qS0,  false :: false :: w' => InL qS0 w'
  | qS0,  true  :: true  :: w' => InL qSd w'
  | qS1,  false :: false :: w' => InL qSd w'
  | qS1,  true  :: true  :: w' => InL qS1 w'
  | qSd,  false :: false :: w' => InL qD1 w'
  | qSd,  true  :: true  :: w' => InL qD1 w'
  | qD0,  false :: true  :: w' => InL qZ0a w'
  | qD0,  true  :: false :: w' => InL qZ0b w'
  | qD1,  false :: true  :: w' => InL qZ1a w'
  | qD1,  true  :: false :: w' => InL qZ1b w'
  | qD2,  false :: true  :: w' => InL qZ0b w'
  | qD2,  true  :: false :: w' => InL qZ0a w'
  | qZ0a, false :: false :: w' => w' <> [] /\ InL qZ1a w'
  | qZ0a, true  :: false :: w' => InL qD0 w'
  | qZ0b, false :: false :: w' => InL qZ0a w'
  | qZ0b, true  :: false :: w' => InL qS0 w'
  | qZ1a, []                   => True
  | qZ1a, [true]               => True
  | qZ1a, false :: true  :: w' => InL qS1 w'
  | qZ1a, true  :: true  :: w' => InL qZ1b w'
  | qZ1b, false :: true  :: w' => InL qD2 w'
  | qZ1b, true  :: true  :: w' => InL qZ0a w'
  | _,    _                    => False
  end.

Definition InL0 (q : Q10) (w : list bool) : Prop :=
  exists u, w = false :: u /\ InL q u.

Definition InL0p (w : list bool) : Prop :=
  exists u, w = false :: u /\ u <> [] /\ InL qZ1a u.

Definition InL1 (q : Q10) (w : list bool) : Prop :=
  exists u, w = true :: u /\ InL q u.

Lemma InL_ne_nil {q : Q10} {w : list bool} (hw : InL q w) (hq : q <> qZ1a) :
  w <> [].
Proof.
  intro hnil. subst w.
  destruct q; cbn [InL] in hw; contradiction.
Qed.

Lemma InL0_ne_nil {q : Q10} {w : list bool} (hw : InL0 q w) : w <> [].
Proof.
  destruct hw as [u [-> _]]. discriminate.
Qed.

Lemma InL0p_ne_nil {w : list bool} (hw : InL0p w) : w <> [].
Proof.
  destruct hw as [u [-> _]]. discriminate.
Qed.

Lemma InL1_ne_nil {q : Q10} {w : list bool} (hw : InL1 q w) : w <> [].
Proof.
  destruct hw as [u [-> _]]. discriminate.
Qed.

Lemma start_in_Sd : InL qSd [false; false; false; true].
Proof. exact I. Qed.

Lemma reload_in_Z0b : InL qZ0b [false; false; false; false; true].
Proof. split; [discriminate | exact I]. Qed.

Lemma S1_eq_ones_double {w : list bool} (hw : InL qS1 w) :
  exists r u, w = ones (2 * r) ++ false :: false :: u /\ InL qSd u.
Proof.
  remember (List.length w) as n eqn:Hn.
  revert w Hn hw.
  induction n as [n IH] using strong_induction.
  intros w Hn hw.
  destruct w as [| [] [| [] w']]; cbn [InL] in hw; try contradiction.
  - destruct (IH (List.length w') ltac:(cbn [List.length] in Hn; lia) w' eq_refl hw)
      as [r [u [-> hu]]].
    exists (S r), u. split; [| exact hu].
    replace (2 * S r) with (S (S (2 * r))) by lia.
    reflexivity.
  - exists 0, w'. split; [reflexivity | exact hw].
Qed.

Lemma ones_double_in_S1 (r : nat) {w : list bool} (hw : InL qSd w) :
  InL qS1 (ones (2 * r) ++ false :: false :: w).
Proof.
  induction r as [| m IH].
  - exact hw.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    exact IH.
Qed.

(* ========================================================================== *)
(* Section 6: Step-Indexed CPS Contracts (14 hb rules + 4 Fb rules)           *)
(* ========================================================================== *)

Definition SafeB (P Q : list bool -> Prop) (k : nat) : Prop :=
  forall w d M u, P w ->
    (forall k' w', k' < k -> Q w' -> Safe k' (retB (sweepBits M (zeros (d + 1) ++ w')) u)) ->
    Safe k (cfgB w d M u).

Definition SafeC (P Q : list bool -> Prop) (k : nat) : Prop :=
  forall w M u, P w ->
    (forall k' w', k' < k -> Q w' -> Safe k' (retB (sweepBits M w') u)) ->
    Safe k (cfgC w M u).

Record Inv (k : nat) : Prop := mkInv {
  (* 6 plain hb rules *)
  inv_Z1a  : SafeB (InL qZ1a)  (InL qZ0b)  k;
  inv_Z0b  : SafeB (InL qZ0b)  (InL qZ1b)  k;
  inv_D1   : SafeB (InL qD1)   (InL qD0)   k;
  inv_D2   : SafeB (InL qD2)   (InL qD1)   k;
  inv_Sd   : SafeB (InL qSd)   (InL qSd)   k;
  inv_S1   : SafeB (InL qS1)   (InL qS0)   k;
  (* 4 shifted 0. hb rules *)
  inv_0Z1a : SafeB InL0p       (InL1 qS1)  k;
  inv_0Z0b : SafeB (InL0 qZ0b) (InL1 qD2)  k;
  inv_0D0  : SafeB (InL0 qD0)  (InL1 qZ1b) k;
  inv_0S0  : SafeB (InL0 qS0)  (InL1 qZ0b) k;
  (* 4 shifted 1. hb rules *)
  inv_1Z0a : SafeB (InL1 qZ0a) (InL0 qD0)  k;
  inv_1Z1b : SafeB (InL1 qZ1b) (InL0 qSd)  k;
  inv_1Sd  : SafeB (InL1 qSd)  (InL0 qZ0a) k;
  inv_1D2  : SafeB (InL1 qD2)  InL0p       k;
  (* 4 Fb rules *)
  inv_fZ1b : SafeC (InL qZ1b)  (InL qSd)   k;
  inv_fZ0a : SafeC (InL qZ0a)  (InL qD1)   k;
  inv_f0D0 : SafeC (InL0 qD0)  (InL0 qZ1b) k;
  inv_f0S0 : SafeC (InL0 qS0)  (InL0 qZ0b) k
}.

Arguments inv_Z1a  {k} _.
Arguments inv_Z0b  {k} _.
Arguments inv_D1   {k} _.
Arguments inv_D2   {k} _.
Arguments inv_Sd   {k} _.
Arguments inv_S1   {k} _.
Arguments inv_0Z1a {k} _.
Arguments inv_0Z0b {k} _.
Arguments inv_0D0  {k} _.
Arguments inv_0S0  {k} _.
Arguments inv_1Z0a {k} _.
Arguments inv_1Z1b {k} _.
Arguments inv_1Sd  {k} _.
Arguments inv_1D2  {k} _.
Arguments inv_fZ1b {k} _.
Arguments inv_fZ0a {k} _.
Arguments inv_f0D0 {k} _.
Arguments inv_f0S0 {k} _.

Lemma sweep_lift_1 {d : nat} {w : list bool} :
  zeros (d + 1 + 1) ++ w = zeros (d + 1) ++ false :: w.
Proof.
  change (d + 1 + 1) with ((d + 1) + 1).
  rewrite zeros_add, <- app_assoc. reflexivity.
Qed.

Lemma sweep_lift_2 {d : nat} {w : list bool} :
  zeros (d + 2 + 1) ++ w = zeros (d + 1) ++ false :: false :: w.
Proof.
  replace (d + 2 + 1) with ((d + 1) + 2) by lia.
  rewrite zeros_add, <- app_assoc. reflexivity.
Qed.

Lemma sweep_lift_3 {d : nat} {w : list bool} :
  zeros (d + 3 + 1) ++ w = zeros (d + 1) ++ false :: false :: false :: w.
Proof.
  replace (d + 3 + 1) with ((d + 1) + 3) by lia.
  rewrite zeros_add, <- app_assoc. reflexivity.
Qed.

Lemma sweep_lift_4 {d : nat} {w : list bool} :
  zeros (d + 4 + 1) ++ w = zeros (d + 1) ++ false :: false :: false :: false :: w.
Proof.
  replace (d + 4 + 1) with ((d + 1) + 4) by lia.
  rewrite zeros_add, <- app_assoc. reflexivity.
Qed.

Lemma sweep_ones_ret (r : nat) (w' : list bool) :
  sweepBits (repeat 0 r) (zeros 2 ++ w') = ones r ++ false :: false :: w'.
Proof.
  pose proof (sweepBits_zeros_rep r [] (false :: false :: w')) as H.
  rewrite app_nil_r in H. exact H.
Qed.

Arguments Safe _ _ : simpl never.

Ltac ptrans_add s1 s2 :=
  eapply ptrans; [exact s1 | rewrite <- Nat.add_assoc; exact s2].

Ltac split_pair w v hw :=
  destruct w as [| [] [| [] v]];
  cbn [InL] in hw;
  try (contradiction || congruence).

Lemma inv_hb_Z1a (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qZ1a) (InL qZ0b) k.
Proof.
  intros w d M u hw hcont.
  split_pair w v hw.
  - (* [] *)
    eapply Safe_of_stepPlus; [exact (step_B_nil d M u) | intros k' hk'].
    exact (hcont k' _ hk' reload_in_Z0b).
  - (* [true] *)
    eapply Safe_of_stepPlus; [exact (step_B_true_nil d M u) | intros k' hk'].
    exact (hcont k' _ hk' reload_in_Z0b).
  - (* true :: true :: v *)
    eapply Safe_of_stepPlus;
      [exact (ptrans (step_B_t (true :: v) d M u)
                     (step_C_t v [] (S1 >> encBuf (d :: M) (S0 >> u)))) |
       intros k1 hk1].
    eapply (inv_fZ1b (ih k1 hk1)); [exact hw |].
    intros k2 w1 hk2 hw1.
    change (Safe k2 (retB (true :: w1) (S1 >> encBuf (d :: M) (S0 >> u)))).
    rewrite retB_of_B_t.
    eapply (inv_1Sd (ih k2 ltac:(lia))); [exists w1; split; [reflexivity | exact hw1] |].
    intros k3 w2 hk3 hw2.
    destruct hw2 as [y [-> hy]].
    rewrite sweep_lift_1.
    exact (hcont k3 (false :: false :: y) ltac:(lia) hy).
  - (* false :: true :: v *)
    eapply Safe_of_stepPlus; [exact (step_B_ft v d M u) | intros k1 hk1].
    eapply (inv_S1 (ih k1 hk1)); [exact hw |].
    intros k2 w' hk2 hw'.
    exact (hcont k2 (true :: false :: w') ltac:(lia) hw').
Qed.

Lemma inv_hb_Z0b (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qZ0b) (InL qZ1b) k.
Proof.
  intros w d M u hw hcont.
  split_pair w v hw.
  - (* true :: false :: v *)
    eapply Safe_of_stepPlus; [exact (step_B_t (false :: v) d M u) | intros k1 hk1].
    eapply (inv_f0S0 (ih k1 hk1)); [exists v; split; [reflexivity | exact hw] |].
    intros k2 w1 hk2 hw1.
    change (Safe k2 (retB w1 (S1 >> encBuf (d :: M) (S0 >> u)))).
    rewrite retB_of_B_t.
    eapply (inv_0Z0b (ih k2 ltac:(lia))); [exact hw1 |].
    intros k3 w2 hk3 hw2.
    destruct hw2 as [y [-> hy]].
    rewrite sweep_lift_1.
    exact (hcont k3 (false :: true :: y) ltac:(lia) hy).
  - (* false :: false :: v *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff v (InL_ne_nil hw ltac:(congruence)) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: v) hk' hw).
Qed.

Lemma inv_hb_D1 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qD1) (InL qD0) k.
Proof.
  intros w d M u hw hcont.
  split_pair w v hw.
  - (* true :: false :: v *)
    split_pair v v2 hw.
    + (* true :: true :: v2 *)
      eapply Safe_of_stepPlus; [exact (step_B_ones_ft 0 (true :: v2) d M u) | intros k1 hk1].
      eapply (inv_1Z0a (ih k1 hk1));
        [exists v2; split; [reflexivity | exact hw] |].
      intros k2 w' hk2 hw'.
      change (Safe k2 (retB (false :: false :: w') (S1 >> encBuf (d :: M) (S0 >> u)))).
      rewrite retB_of_B_t.
      eapply Safe_of_stepPlus;
        [exact (step_B_ff w' (InL0_ne_nil hw') (d + 1) M u) | intros k3 hk3].
      destruct hw' as [y [-> hy]].
      rewrite sweep_lift_1.
      exact (hcont k3 (false :: true :: true :: false :: y) ltac:(lia) hy).
    + (* false :: true :: v2 *)
      eapply Safe_of_stepPlus;
        [exact (ptrans (step_B_ones_ff 0 (true :: v2) ltac:(discriminate) d M u)
                       (step_B_ft (true :: v2) (d + 1) M u)) |
         intros k1 hk1].
      eapply (inv_1D2 (ih k1 hk1));
        [exists v2; split; [reflexivity | exact hw] |].
      intros k2 w' hk2 hw'.
      destruct hw' as [y [-> [hne hy]]].
      change (Safe k2 (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: false :: y)) u)).
      rewrite sweep_lift_1.
      exact (hcont k2 (false :: true :: false :: false :: y) ltac:(lia) (conj hne hy)).
  - (* false :: true :: v *)
    eapply Safe_of_stepPlus; [exact (step_B_ft v d M u) | intros k1 hk1].
    eapply (inv_Z1a (ih k1 hk1)); [exact hw |].
    intros k2 w' hk2 hw'.
    exact (hcont k2 (true :: false :: w') ltac:(lia) hw').
Qed.

Lemma inv_hb_D2 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qD2) (InL qD1) k.
Proof.
  intros w d M u hw hcont.
  split_pair w v hw.
  - (* true :: false :: v *)
    split_pair v v2 hw.
    + (* true :: false :: v2 *)
      eapply Safe_of_stepPlus; [exact (step_B_ones_ft 0 (false :: v2) d M u) | intros k1 hk1].
      eapply (inv_0D0 (ih k1 hk1));
        [exists v2; split; [reflexivity | exact hw] |].
      intros k2 w' hk2 hw'.
      change (Safe k2 (retB (false :: false :: w') (S1 >> encBuf (d :: M) (S0 >> u)))).
      rewrite retB_of_B_t.
      eapply Safe_of_stepPlus;
        [exact (step_B_ff w' (InL1_ne_nil hw') (d + 1) M u) | intros k3 hk3].
      destruct hw' as [y [-> hy]].
      rewrite sweep_lift_1.
      exact (hcont k3 (false :: true :: true :: true :: y) ltac:(lia) hy).
    + (* false :: false :: v2 *)
      eapply Safe_of_stepPlus;
        [exact (ptrans (step_B_ones_ff 0 (false :: v2) ltac:(discriminate) d M u)
                       (step_B_ft (false :: v2) (d + 1) M u)) |
         intros k1 hk1].
      destruct hw as [hne hy].
      eapply (inv_0Z1a (ih k1 hk1));
        [exists v2; split; [reflexivity | split; [exact hne | exact hy]] |].
      intros k2 w' hk2 hw'.
      destruct hw' as [y [-> hy']].
      change (Safe k2 (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: true :: y)) u)).
      rewrite sweep_lift_1.
      exact (hcont k2 (false :: true :: false :: true :: y) ltac:(lia) hy').
  - (* false :: true :: v *)
    eapply Safe_of_stepPlus; [exact (step_B_ft v d M u) | intros k1 hk1].
    eapply (inv_Z0b (ih k1 hk1)); [exact hw |].
    intros k2 w' hk2 hw'.
    exact (hcont k2 (true :: false :: w') ltac:(lia) hw').
Qed.

Lemma inv_hb_Sd (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qSd) (InL qSd) k.
Proof.
  intros w d M u hw hcont.
  split_pair w v hw.
  - (* true :: true :: v *)
    split_pair v v2 hw.
    + (* true :: false :: v2 *)
      split_pair v2 v3 hw.
      * (* true :: true :: v3 *)
        eapply Safe_of_stepPlus; [exact (step_B_ones_ft 2 (true :: v3) d M u) | intros k1 hk1].
        eapply (inv_1Z0a (ih k1 hk1));
          [exists v3; split; [reflexivity | exact hw] |].
        intros k2 w1 hk2 hw1.
        change (Safe k2 (retB (true :: true :: false :: false :: w1) (S1 >> encBuf (d :: M) (S0 >> u)))).
        rewrite retB_of_B_t.
        eapply Safe_of_stepPlus;
          [ptrans_add (step_B_ones_ff 1 w1 (InL0_ne_nil hw1) (d + 1) M u)
                      (step_B_ones_ft 0 w1 (d + 2) M u) |
           intros k3 hk3].
        eapply (inv_0D0 (ih k3 ltac:(lia))); [exact hw1 |].
        intros k4 w2 hk4 hw2.
        change (Safe k4 (retB (false :: false :: w2) (S1 >> encBuf ((d + 2) :: M) (S0 >> u)))).
        rewrite retB_of_B_t, <- Nat.add_assoc.
        eapply Safe_of_stepPlus;
          [exact (step_B_ff w2 (InL1_ne_nil hw2) (d + 3) M u) | intros k5 hk5].
        destruct hw2 as [y [-> hy]].
        rewrite sweep_lift_3.
        exact (hcont k5 (false :: false :: false :: true :: true :: true :: y) ltac:(lia) hy).
      * (* false :: true :: v3 *)
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_B_ones_ff 2 (true :: v3) ltac:(discriminate) d M u)
                         (step_B_ones_ft 1 (true :: v3) (d + 1) M u)) |
           intros k1 hk1].
        eapply (inv_1D2 (ih k1 hk1));
          [exists v3; split; [reflexivity | exact hw] |].
        intros k2 w1 hk2 hw1.
        change (Safe k2 (retB (true :: false :: false :: w1) (S1 >> encBuf ((d + 1) :: M) (S0 >> u)))).
        rewrite retB_of_B_t, <- Nat.add_assoc.
        eapply Safe_of_stepPlus;
          [ptrans_add (step_B_ones_ff 0 w1 (InL0p_ne_nil hw1) (d + 2) M u)
                      (step_B_ft w1 (d + 3) M u) |
           intros k3 hk3].
        eapply (inv_0Z1a (ih k3 ltac:(lia))); [exact hw1 |].
        intros k4 w2 hk4 hw2.
        destruct hw2 as [y [-> hy]].
        change (Safe k4 (retB (sweepBits M (zeros (d + 3 + 1) ++ true :: false :: true :: y)) u)).
        rewrite sweep_lift_3.
        exact (hcont k4 (false :: false :: false :: true :: false :: true :: y) ltac:(lia) hy).
    + (* false :: true :: v2 *)
      eapply Safe_of_stepPlus; [exact (step_B_ones_ft 1 v2 d M u) | intros k1 hk1].
      eapply (inv_Z1a (ih k1 hk1)); [exact hw |].
      intros k2 w1 hk2 hw1.
      change (Safe k2 (retB (true :: false :: false :: w1) (S1 >> encBuf (d :: M) (S0 >> u)))).
      rewrite retB_of_B_t.
      eapply Safe_of_stepPlus;
        [ptrans_add (step_B_ones_ff 0 w1 (InL_ne_nil hw1 ltac:(congruence)) (d + 1) M u)
                    (step_B_ft w1 (d + 2) M u) |
         intros k3 hk3].
      eapply (inv_Z0b (ih k3 ltac:(lia))); [exact hw1 |].
      intros k4 w2 hk4 hw2.
      change (Safe k4 (retB (sweepBits M (zeros (d + 2 + 1) ++ true :: false :: w2)) u)).
      rewrite sweep_lift_2.
      exact (hcont k4 (false :: false :: true :: false :: w2) ltac:(lia) hw2).
  - (* false :: false :: v *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff v (InL_ne_nil hw ltac:(congruence)) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: v) hk' hw).
Qed.

Lemma inv_hb_S1 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL qS1) (InL qS0) k.
Proof.
  intros w d M u hw hcont.
  destruct (S1_eq_ones_double hw) as [r [v [-> hv]]].
  destruct r as [| r'].
  - eapply Safe_of_stepPlus;
      [exact (step_B_ff v (InL_ne_nil hv ltac:(congruence)) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: v) hk' hv).
  - replace (2 * S r') with (S (S (2 * r'))) by lia.
    cbn [ones List.app].
    eapply Safe_of_stepPlus;
      [exact (ptrans (step_B_ones_ff (S (2 * r')) v (InL_ne_nil hv ltac:(congruence)) d M u)
                     (step_B_ones_ft (2 * r') v (d + 1) M u)) |
       intros k1 hk1].
    eapply (inv_Sd (ih k1 hk1)); [exact hv |].
    intros k2 w1 hk2 hw1.
    rewrite sweep_ones_ret, retB_of_B_t, <- Nat.add_assoc.
    eapply (inv_S1 (ih k2 ltac:(lia))); [exact (ones_double_in_S1 r' hw1) |].
    intros k3 w2 hk3 hw2.
    rewrite sweep_lift_2.
    exact (hcont k3 (false :: false :: w2) ltac:(lia) hw2).
Qed.

Lemma inv_hb_0Z1a (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB InL0p (InL1 qS1) k.
Proof.
  intros w d M u hw hcont.
  destruct hw as [v [-> [hne hv]]].
  split_pair v v' hv.
  - (* [true] *)
    eapply Safe_of_stepPlus;
      [exact (ptrans (step_B_ft [] d M u) (step_B_nil 0 ((d + 1) :: M) u)) |
       intros k1 hk1].
    exact (hcont k1 (true :: false :: false :: false :: false :: false :: [true]) hk1
             (ex_intro _ [false; false; false; false; false; true] (conj eq_refl I))).
  - (* true :: true :: v' *)
    eapply Safe_of_stepPlus; [exact (step_B_ft (true :: v') d M u) | intros k1 hk1].
    eapply (inv_1Z1b (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (true :: false :: false :: y) ltac:(lia)
             (ex_intro _ (false :: false :: y) (conj eq_refl hy))).
  - (* false :: true :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff (true :: v') ltac:(discriminate) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: true :: v') hk'
             (ex_intro _ (true :: true :: v') (conj eq_refl hv))).
Qed.

Lemma inv_hb_0Z0b (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL0 qZ0b) (InL1 qD2) k.
Proof.
  intros w d M u hw hcont.
  destruct hw as [v [-> hv]].
  split_pair v v' hv.
  - (* true :: false :: v' *)
    eapply Safe_of_stepPlus; [exact (step_B_ft (false :: v') d M u) | intros k1 hk1].
    eapply (inv_0S0 (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (true :: false :: true :: y) ltac:(lia)
             (ex_intro _ (false :: true :: y) (conj eq_refl hy))).
  - (* false :: false :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff (false :: v') ltac:(discriminate) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: false :: v') hk'
             (ex_intro _ (true :: false :: v') (conj eq_refl hv))).
Qed.

Lemma inv_hb_0D0 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL0 qD0) (InL1 qZ1b) k.
Proof.
  intros w d M u hw hcont.
  destruct hw as [v [-> hv]].
  split_pair v v' hv.
  - (* true :: false :: v' *)
    eapply Safe_of_stepPlus; [exact (step_B_ft (false :: v') d M u) | intros k1 hk1].
    eapply (inv_0Z0b (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (true :: false :: true :: y) ltac:(lia)
             (ex_intro _ (false :: true :: y) (conj eq_refl hy))).
  - (* false :: true :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff (true :: v') ltac:(discriminate) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: true :: v') hk'
             (ex_intro _ (true :: true :: v') (conj eq_refl hv))).
Qed.

Lemma inv_hb_0S0 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL0 qS0) (InL1 qZ0b) k.
Proof.
  intros w d M u hw hcont.
  destruct hw as [v [-> hv]].
  split_pair v v' hv.
  - (* true :: true :: v' *)
    eapply Safe_of_stepPlus; [exact (step_B_ft (true :: v') d M u) | intros k1 hk1].
    eapply (inv_1Sd (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (true :: false :: false :: y) ltac:(lia)
             (ex_intro _ (false :: false :: y) (conj eq_refl hy))).
  - (* false :: false :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_B_ff (false :: v') ltac:(discriminate) d M u) | intros k' hk'].
    exact (hcont k' (true :: true :: false :: v') hk'
             (ex_intro _ (true :: false :: v') (conj eq_refl hv))).
Qed.

Lemma inv_hb_1Z0a (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL1 qZ0a) (InL0 qD0) k.
Proof.
  intros w d M u [v [-> hv]] hcont.
  eapply Safe_of_stepPlus; [exact (step_B_t v d M u) | intros k1 hk1].
  eapply (inv_fZ0a (ih k1 hk1)); [exact hv |].
  intros k2 w1 hk2 hw1.
  change (Safe k2 (retB w1 (S1 >> encBuf (d :: M) (S0 >> u)))).
  rewrite retB_of_B_t.
  eapply (inv_D1 (ih k2 ltac:(lia))); [exact hw1 |].
  intros k3 w2 hk3 hw2.
  rewrite sweep_lift_1.
  exact (hcont k3 (false :: w2) ltac:(lia) (ex_intro _ w2 (conj eq_refl hw2))).
Qed.

Lemma inv_hb_1Z1b (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL1 qZ1b) (InL0 qSd) k.
Proof.
  intros w d M u [v [-> hv]] hcont.
  eapply Safe_of_stepPlus; [exact (step_B_t v d M u) | intros k1 hk1].
  eapply (inv_fZ1b (ih k1 hk1)); [exact hv |].
  intros k2 w1 hk2 hw1.
  change (Safe k2 (retB w1 (S1 >> encBuf (d :: M) (S0 >> u)))).
  rewrite retB_of_B_t.
  eapply (inv_Sd (ih k2 ltac:(lia))); [exact hw1 |].
  intros k3 w2 hk3 hw2.
  rewrite sweep_lift_1.
  exact (hcont k3 (false :: w2) ltac:(lia) (ex_intro _ w2 (conj eq_refl hw2))).
Qed.

Lemma inv_hb_1Sd (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL1 qSd) (InL0 qZ0a) k.
Proof.
  intros w d M u [v [-> hv]] hcont.
  split_pair v v1 hv.
  - (* true :: true :: v1 *)
    split_pair v1 v2 hv.
    + (* true :: false :: v2 *)
      split_pair v2 v3 hv.
      * (* true :: true :: v3 *)
        eapply Safe_of_stepPlus; [exact (step_B_ones_ft 3 (true :: v3) d M u) | intros k1 hk1].
        eapply (inv_1Z0a (ih k1 hk1)); [exists v3; split; [reflexivity | exact hv] |].
        intros k2 w1 hk2 hw1.
        change (Safe k2 (retB (true :: true :: true :: false :: false :: w1)
                              (S1 >> encBuf (d :: M) (S0 >> u)))).
        rewrite retB_of_B_t.
        eapply Safe_of_stepPlus;
          [ptrans_add (step_B_ones_ff 2 w1 (InL0_ne_nil hw1) (d + 1) M u)
                      (step_B_ones_ft 1 w1 (d + 2) M u) |
           intros k3 hk3].
        eapply (inv_0D0 (ih k3 ltac:(lia))); [exact hw1 |].
        intros k4 w2 hk4 hw2.
        change (Safe k4 (retB (true :: false :: false :: w2)
                              (S1 >> encBuf ((d + 2) :: M) (S0 >> u)))).
        rewrite retB_of_B_t, <- Nat.add_assoc.
        eapply Safe_of_stepPlus;
          [ptrans_add (step_B_ones_ff 0 w2 (InL1_ne_nil hw2) (d + 3) M u)
                      (step_B_ft w2 (d + 4) M u) |
           intros k5 hk5].
        eapply (inv_1Z1b (ih k5 ltac:(lia))); [exact hw2 |].
        intros k6 w3 hk6 hw3.
        destruct hw3 as [y [-> hy]].
        change (Safe k6 (retB (sweepBits M (zeros (d + 4 + 1) ++ true :: false :: false :: y)) u)).
        rewrite sweep_lift_4.
        apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hy]]].
      * (* false :: true :: v3 *)
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_B_ones_ff 3 (true :: v3) ltac:(discriminate) d M u)
                         (step_B_ones_ft 2 (true :: v3) (d + 1) M u)) |
           intros k1 hk1].
        eapply (inv_1D2 (ih k1 hk1)); [exists v3; split; [reflexivity | exact hv] |].
        intros k2 w1 hk2 hw1.
        change (Safe k2 (retB (true :: true :: false :: false :: w1)
                              (S1 >> encBuf ((d + 1) :: M) (S0 >> u)))).
        rewrite retB_of_B_t, <- Nat.add_assoc.
        eapply Safe_of_stepPlus;
          [ptrans_add (step_B_ones_ff 1 w1 (InL0p_ne_nil hw1) (d + 2) M u)
                      (step_B_ones_ft 0 w1 (d + 3) M u) |
           intros k3 hk3].
        eapply (inv_0Z1a (ih k3 ltac:(lia))); [exact hw1 |].
        intros k4 w2 hk4 hw2.
        change (Safe k4 (retB (false :: false :: w2)
                              (S1 >> encBuf ((d + 3) :: M) (S0 >> u)))).
        rewrite retB_of_B_t, <- Nat.add_assoc.
        eapply Safe_of_stepPlus;
          [exact (step_B_ff w2 (InL1_ne_nil hw2) (d + 4) M u) | intros k5 hk5].
        destruct hw2 as [y [-> hy]].
        rewrite sweep_lift_4.
        apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hy]]].
    + (* false :: true :: v2 *)
      eapply Safe_of_stepPlus; [exact (step_B_ones_ft 2 v2 d M u) | intros k1 hk1].
      eapply (inv_Z1a (ih k1 hk1)); [exact hv |].
      intros k2 w1 hk2 hw1.
      change (Safe k2 (retB (true :: true :: false :: false :: w1)
                            (S1 >> encBuf (d :: M) (S0 >> u)))).
      rewrite retB_of_B_t.
      eapply Safe_of_stepPlus;
        [ptrans_add (step_B_ones_ff 1 w1 (InL_ne_nil hw1 ltac:(congruence)) (d + 1) M u)
                    (step_B_ones_ft 0 w1 (d + 2) M u) |
         intros k3 hk3].
      eapply (inv_Z0b (ih k3 ltac:(lia))); [exact hw1 |].
      intros k4 w2 hk4 hw2.
      change (Safe k4 (retB (false :: false :: w2)
                            (S1 >> encBuf ((d + 2) :: M) (S0 >> u)))).
      rewrite retB_of_B_t, <- Nat.add_assoc.
      eapply Safe_of_stepPlus;
        [exact (step_B_ff w2 (InL_ne_nil hw2 ltac:(congruence)) (d + 3) M u) | intros k5 hk5].
      rewrite sweep_lift_3.
      apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hw2]]].
  - (* false :: false :: v1 *)
    eapply Safe_of_stepPlus;
      [exact (ptrans (step_B_ones_ff 0 v1 (InL_ne_nil hv ltac:(congruence)) d M u)
                     (step_B_ft v1 (d + 1) M u)) |
       intros k1 hk1].
    eapply (inv_D1 (ih k1 hk1)); [exact hv |].
    intros k2 w' hk2 hw'.
    change (Safe k2 (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: w')) u)).
    rewrite sweep_lift_1.
    exact (hcont k2 (false :: true :: false :: w') ltac:(lia)
             (ex_intro _ (true :: false :: w') (conj eq_refl hw'))).
Qed.

Lemma inv_hb_1D2 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeB (InL1 qD2) InL0p k.
Proof.
  intros w d M u [v [-> hv]] hcont.
  split_pair v v1 hv.
  - (* true :: false :: v1 *)
    split_pair v1 v2 hv.
    + (* true :: false :: v2 *)
      eapply Safe_of_stepPlus; [exact (step_B_ones_ft 1 (false :: v2) d M u) | intros k1 hk1].
      eapply (inv_0D0 (ih k1 hk1)); [exists v2; split; [reflexivity | exact hv] |].
      intros k2 w1 hk2 hw1.
      change (Safe k2 (retB (true :: false :: false :: w1) (S1 >> encBuf (d :: M) (S0 >> u)))).
      rewrite retB_of_B_t.
      eapply Safe_of_stepPlus;
        [ptrans_add (step_B_ones_ff 0 w1 (InL1_ne_nil hw1) (d + 1) M u)
                    (step_B_ft w1 (d + 2) M u) |
         intros k3 hk3].
      eapply (inv_1Z1b (ih k3 ltac:(lia))); [exact hw1 |].
      intros k4 w2 hk4 hw2.
      destruct hw2 as [y [-> hy]].
      change (Safe k4 (retB (sweepBits M (zeros (d + 2 + 1) ++ true :: false :: false :: y)) u)).
      rewrite sweep_lift_2.
      apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hy]]].
    + (* false :: false :: v2 *)
      eapply Safe_of_stepPlus;
        [exact (ptrans (step_B_ones_ff 1 (false :: v2) ltac:(discriminate) d M u)
                       (step_B_ones_ft 0 (false :: v2) (d + 1) M u)) |
         intros k1 hk1].
      destruct hv as [hne hy].
      eapply (inv_0Z1a (ih k1 hk1));
        [exists v2; split; [reflexivity | split; [exact hne | exact hy]] |].
      intros k2 w1 hk2 hw1.
      change (Safe k2 (retB (false :: false :: w1) (S1 >> encBuf ((d + 1) :: M) (S0 >> u)))).
      rewrite retB_of_B_t, <- Nat.add_assoc.
      eapply Safe_of_stepPlus;
        [exact (step_B_ff w1 (InL1_ne_nil hw1) (d + 2) M u) | intros k3 hk3].
      destruct hw1 as [y [-> hy']].
      rewrite sweep_lift_2.
      apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hy']]].
  - (* false :: true :: v1 *)
    eapply Safe_of_stepPlus; [exact (step_B_ones_ft 0 v1 d M u) | intros k1 hk1].
    eapply (inv_Z0b (ih k1 hk1)); [exact hv |].
    intros k2 w' hk2 hw'.
    change (Safe k2 (retB (false :: false :: w') (S1 >> encBuf (d :: M) (S0 >> u)))).
    rewrite retB_of_B_t.
    eapply Safe_of_stepPlus;
      [exact (step_B_ff w' (InL_ne_nil hw' ltac:(congruence)) (d + 1) M u) | intros k3 hk3].
    rewrite sweep_lift_1.
    apply hcont; [lia | eexists; split; [reflexivity | split; [discriminate | exact hw']]].
Qed.

Lemma inv_fb_Z1b (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeC (InL qZ1b) (InL qSd) k.
Proof.
  intros w M u hw hcont.
  split_pair w v hw.
  - (* true :: true :: v *)
    eapply Safe_of_stepPlus;
      [exact (ptrans (step_C_t (true :: v) M u) (step_C_t v (0 :: M) u)) |
       intros k1 hk1].
    eapply (inv_fZ0a (ih k1 hk1)); [exact hw |].
    intros k2 w' hk2 hw'.
    exact (hcont k2 (true :: true :: w') ltac:(lia) hw').
  - (* false :: true :: v *)
    eapply Safe_of_stepPlus; [exact (step_C_ft v M u) | intros k1 hk1].
    eapply (inv_D2 (ih k1 hk1)); [exact hw |].
    intros k2 w' hk2 hw'.
    exact (hcont k2 (false :: false :: w') ltac:(lia) hw').
Qed.

Lemma inv_fb_Z0a (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeC (InL qZ0a) (InL qD1) k.
Proof.
  intros w M u hw hcont.
  split_pair w v hw.
  - (* true :: false :: v *)
    eapply Safe_of_stepPlus; [exact (step_C_t (false :: v) M u) | intros k1 hk1].
    eapply (inv_f0D0 (ih k1 hk1)); [exists v; split; [reflexivity | exact hw] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (true :: false :: y) ltac:(lia) hy).
  - (* false :: false :: v *)
    destruct hw as [hne hy].
    eapply Safe_of_stepPlus; [exact (step_C_ff v hne M u) | intros k' hk'].
    exact (hcont k' (false :: true :: v) hk' hy).
Qed.

Lemma inv_fb_0D0 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeC (InL0 qD0) (InL0 qZ1b) k.
Proof.
  intros w M u [v [-> hv]] hcont.
  split_pair v v' hv.
  - (* true :: false :: v' *)
    eapply Safe_of_stepPlus; [exact (step_C_ft (false :: v') M u) | intros k1 hk1].
    eapply (inv_0Z0b (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (false :: false :: true :: y) ltac:(lia)
             (ex_intro _ (false :: true :: y) (conj eq_refl hy))).
  - (* false :: true :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_C_ff (true :: v') ltac:(discriminate) M u) | intros k' hk'].
    exact (hcont k' (false :: true :: true :: v') hk'
             (ex_intro _ (true :: true :: v') (conj eq_refl hv))).
Qed.

Lemma inv_fb_0S0 (k : nat) (ih : forall k', k' < k -> Inv k') :
  SafeC (InL0 qS0) (InL0 qZ0b) k.
Proof.
  intros w M u [v [-> hv]] hcont.
  split_pair v v' hv.
  - (* true :: true :: v' *)
    eapply Safe_of_stepPlus; [exact (step_C_ft (true :: v') M u) | intros k1 hk1].
    eapply (inv_1Sd (ih k1 hk1)); [exists v'; split; [reflexivity | exact hv] |].
    intros k2 w' hk2 hw'.
    destruct hw' as [y [-> hy]].
    exact (hcont k2 (false :: false :: false :: y) ltac:(lia)
             (ex_intro _ (false :: false :: y) (conj eq_refl hy))).
  - (* false :: false :: v' *)
    eapply Safe_of_stepPlus;
      [exact (step_C_ff (false :: v') ltac:(discriminate) M u) | intros k' hk'].
    exact (hcont k' (false :: true :: false :: v') hk'
             (ex_intro _ (true :: false :: v') (conj eq_refl hv))).
Qed.

Lemma inv_holds (k : nat) : Inv k.
Proof.
  induction k as [k ih] using strong_induction.
  exact (mkInv k
    (inv_hb_Z1a k ih) (inv_hb_Z0b k ih) (inv_hb_D1 k ih)
    (inv_hb_D2 k ih) (inv_hb_Sd k ih) (inv_hb_S1 k ih)
    (inv_hb_0Z1a k ih) (inv_hb_0Z0b k ih) (inv_hb_0D0 k ih) (inv_hb_0S0 k ih)
    (inv_hb_1Z0a k ih) (inv_hb_1Z1b k ih) (inv_hb_1Sd k ih) (inv_hb_1D2 k ih)
    (inv_fb_Z1b k ih) (inv_fb_Z0a k ih) (inv_fb_0D0 k ih) (inv_fb_0S0 k ih)).
Qed.

Lemma top_Sd_safe (k : nat) : forall w, InL qSd w -> Safe k (retB w 0inf).
Proof.
  induction k as [k ih] using strong_induction.
  intros w hw.
  split_pair w v hw.
  - (* true :: true :: v *)
    split_pair v v2 hw.
    + (* true :: false :: v2 *)
      split_pair v2 v3 hw.
      * (* true :: true :: v3 *)
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_top_t (true :: true :: false :: true :: true :: v3))
                         (step_C_ones_ft 2 (true :: v3) [] (S1 >> 0inf))) |
           intros k1 hk1].
        eapply (inv_1Z0a (inv_holds k1));
          [exists v3; split; [reflexivity | exact hw] |].
        intros k2 w1 hk2 hw1.
        change (Safe k2 (retB (true :: true :: false :: false :: w1) (S1 >> 0inf))).
        rewrite retB_of_top_t.
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_B_ones_ff 1 w1 (InL0_ne_nil hw1) 0 [] 0inf)
                         (step_B_ones_ft 0 w1 1 [] 0inf)) |
           intros k3 hk3].
        eapply (inv_0D0 (inv_holds k3)); [exact hw1 |].
        intros k4 w2 hk4 hw2.
        change (Safe k4 (retB (false :: false :: w2) (S1 >> encBuf [1] (S0 >> 0inf)))).
        rewrite retB_of_B_t.
        eapply Safe_of_stepPlus;
          [exact (step_B_ff w2 (InL1_ne_nil hw2) 2 [] 0inf) | intros k5 hk5].
        destruct hw2 as [y [-> hy]].
        exact (ih k5 ltac:(lia) (false :: false :: false :: true :: true :: true :: y) hy).
      * (* false :: true :: v3 *)
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_top_t (true :: true :: false :: false :: true :: v3))
                         (step_C_ones_ff 2 (true :: v3) ltac:(discriminate) [] (S1 >> 0inf))) |
           intros k1 hk1].
        change (Safe k1 (retB (true :: true :: false :: true :: true :: v3) (S1 >> 0inf))).
        rewrite retB_of_top_t.
        eapply Safe_of_stepPlus; [exact (step_B_ones_ft 1 (true :: v3) 0 [] 0inf) | intros k2 hk2].
        eapply (inv_1D2 (inv_holds k2));
          [exists v3; split; [reflexivity | exact hw] |].
        intros k3 w1 hk3 hw1.
        change (Safe k3 (retB (true :: false :: false :: w1) (S1 >> encBuf [0] (S0 >> 0inf)))).
        rewrite retB_of_B_t.
        eapply Safe_of_stepPlus;
          [exact (ptrans (step_B_ones_ff 0 w1 (InL0p_ne_nil hw1) 1 [] 0inf)
                         (step_B_ft w1 2 [] 0inf)) |
           intros k4 hk4].
        eapply (inv_0Z1a (inv_holds k4)); [exact hw1 |].
        intros k5 w2 hk5 hw2.
        destruct hw2 as [y [-> hy]].
        exact (ih k5 ltac:(lia) (false :: false :: false :: true :: false :: true :: y) hy).
    + (* false :: true :: v2 *)
      eapply Safe_of_stepPlus;
        [exact (ptrans (step_top_t (true :: false :: true :: v2))
                       (step_C_ones_ft 1 v2 [] (S1 >> 0inf))) |
         intros k1 hk1].
      eapply (inv_Z1a (inv_holds k1)); [exact hw |].
      intros k2 w1 hk2 hw1.
      change (Safe k2 (retB (true :: false :: false :: w1) (S1 >> 0inf))).
      rewrite retB_of_top_t.
      eapply Safe_of_stepPlus;
        [exact (ptrans (step_B_ones_ff 0 w1 (InL_ne_nil hw1 ltac:(congruence)) 0 [] 0inf)
                       (step_B_ft w1 1 [] 0inf)) |
         intros k3 hk3].
      eapply (inv_Z0b (inv_holds k3)); [exact hw1 |].
      intros k4 w2 hk4 hw2.
      exact (ih k4 ltac:(lia) (false :: false :: true :: false :: w2) hw2).
  - (* false :: false :: v *)
    eapply Safe_of_stepPlus;
      [exact (step_top_ff v (InL_ne_nil hw ltac:(congruence))) | intros k1 hk1].
    exact (ih k1 hk1 (true :: true :: v) hw).
Qed.

Theorem nonhalt_internal : ~ halts tm c0.
Proof.
  eapply nonhalt_of_forall_safe.
  - exact init_reaches_start.
  - intro k. exact (top_Sd_safe k [false; false; false; true] start_in_Sd).
Qed.

End Internal.

Theorem nonhalt : ~ halts tm c0.
Proof. exact Internal.nonhalt_internal. Qed.
