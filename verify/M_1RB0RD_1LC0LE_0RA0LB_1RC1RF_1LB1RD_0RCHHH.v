(* 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC--- never halts. *)

From Coq Require Import Bool List Lists.Streams PeanoNat Lia String.
From BusyCoq Require Import Individual62.
Import ListNotations.

Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---".
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

Arguments Safe _ _ : simpl never.

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
(* Section 3: Prefix-Separator Bitstring Transducer & Symbolic Micro-Steps    *)
(* ========================================================================== *)

Fixpoint encBits (xs : list bool) : side :=
  match xs with
  | [] => 0inf
  | false :: xs' => S0 >> encBits xs'
  | true :: rest =>
    match rest with
    | [] => S1 >> 0inf
    | false :: xs' => S1 >> S0 >> encBits xs'
    | true :: xs' => S1 >> S1 >> S0 >> encBits xs'
    end
  end.

Lemma encBits_nil : encBits [] = 0inf.
Proof. reflexivity. Qed.

Lemma encBits_f (xs : list bool) : encBits (false :: xs) = S0 >> encBits xs.
Proof. reflexivity. Qed.

Lemma encBits_tf (xs : list bool) :
  encBits (true :: false :: xs) = S1 >> S0 >> encBits xs.
Proof. reflexivity. Qed.

Lemma encBits_tt (xs : list bool) :
  encBits (true :: true :: xs) = S1 >> S1 >> S0 >> encBits xs.
Proof. reflexivity. Qed.

Definition cfgTop (xs : list bool) : Q * tape :=
  encBits (true :: false :: xs) {{B}}> 0inf.

Definition cfgB (xs : list bool) (r : side) : Q * tape :=
  encBits xs {{B}}> (S0 >> r).

Definition cfgD (xs : list bool) (r : side) : Q * tape :=
  encBits (false :: false :: xs) {{D}}> r.

Definition cfgA (xs : list bool) (r : side) : Q * tape :=
  encBits (false :: xs) {{A}}> r.

Lemma init_to_top : c0 -[ tm ]->+ cfgTop [].
Proof.
  unfold c0, tape0, cfgTop.
  rewrite encBits_tf, encBits_nil.
  run_steps.
Qed.

Lemma top_enter (xs : list bool) :
  cfgTop xs -[ tm ]->+ cfgB xs ([S0; S1] *> 0inf).
Proof.
  unfold cfgTop, cfgB.
  rewrite encBits_tf.
  run_steps.
Qed.

Lemma top_ret_A (xs : list bool) :
  cfgA xs ([S0; S1] *> 0inf) -[ tm ]->+ cfgTop (true :: true :: xs).
Proof.
  unfold cfgA, cfgTop.
  rewrite encBits_f, encBits_tf, encBits_tt.
  run_steps.
Qed.

Lemma top_ret_D (xs : list bool) :
  cfgD xs ([S0; S1] *> 0inf) -[ tm ]->+ cfgB xs ([S1] *> 0inf).
Proof.
  unfold cfgD, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma top_ret_DD (xs : list bool) :
  cfgD xs ([S1] *> 0inf) -[ tm ]->+ cfgTop (false :: true :: false :: false :: xs).
Proof.
  unfold cfgD, cfgTop.
  repeat rewrite encBits_f; repeat rewrite encBits_tf; repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma top_ret_DA (xs : list bool) :
  cfgA xs ([S1] *> 0inf) -[ tm ]->+ cfgTop (true :: false :: false :: xs).
Proof.
  unfold cfgA, cfgTop.
  repeat rewrite encBits_f; repeat rewrite encBits_tf; repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma box_emp (r : side) :
  cfgB [] r -[ tm ]->+ cfgD [] r.
Proof.
  unfold cfgB, cfgD.
  repeat rewrite encBits_f; rewrite encBits_nil.
  run_steps.
Qed.

Lemma box_0100 (u : list bool) (r : side) :
  cfgB (false :: true :: false :: false :: u) r -[ tm ]->+
  cfgD (true :: false :: false :: u) r.
Proof.
  unfold cfgB, cfgD.
  repeat (rewrite encBits_f || rewrite encBits_tf).
  run_steps.
Qed.

Lemma box_100 (u : list bool) (r : side) :
  cfgB (true :: false :: false :: u) r -[ tm ]->+ cfgB u ([S1; S0; S0] *> r).
Proof.
  unfold cfgB.
  repeat (rewrite encBits_f || rewrite encBits_tf).
  run_steps.
Qed.

Lemma ret_100_D (u : list bool) (r : side) :
  cfgD u ([S1; S0; S0] *> r) -[ tm ]->+ cfgA (false :: true :: false :: false :: u) r.
Proof.
  unfold cfgD, cfgA.
  repeat (rewrite encBits_f || rewrite encBits_tf).
  run_steps.
Qed.

Lemma ret_100_A (u : list bool) (r : side) :
  cfgA u ([S1; S0; S0] *> r) -[ tm ]->+ cfgA (true :: false :: false :: u) r.
Proof.
  unfold cfgA.
  repeat (rewrite encBits_f || rewrite encBits_tf).
  run_steps.
Qed.

Lemma box_110_emp (r : side) :
  cfgB [true; true] r -[ tm ]->+ cfgD [false; true; false; false] r.
Proof.
  unfold cfgB, cfgD.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f || rewrite encBits_nil).
  run_steps.
Qed.

Lemma box_110_0100 (v : list bool) (r : side) :
  cfgB (true :: true :: false :: true :: false :: false :: v) r -[ tm ]->+
  cfgB v ([S1; S0; S0; S1; S0; S0; S1] *> r).
Proof.
  unfold cfgB.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_110_0100_D (v : list bool) (r : side) :
  cfgD v ([S1; S0; S0; S1; S0; S0; S1] *> r) -[ tm ]->+
  cfgD (true :: false :: false :: false :: true :: false :: false :: v) r.
Proof.
  unfold cfgD.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_110_0100_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S0; S1; S0; S0; S1] *> r) -[ tm ]->+
  cfgD (true :: false :: false :: true :: false :: false :: v) r.
Proof.
  unfold cfgA, cfgD.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma box_110_110 (z : list bool) (r : side) :
  cfgB (true :: true :: true :: true :: z) r -[ tm ]->+
  cfgB (true :: true :: z) ([S0; S1; S1] *> r).
Proof.
  unfold cfgB.
  repeat rewrite encBits_tt.
  run_steps.
Qed.

Lemma ret_110_110_A (u : list bool) (r : side) :
  cfgA u ([S0; S1; S1] *> r) -[ tm ]->+ cfgA (true :: true :: u) r.
Proof.
  unfold cfgA.
  repeat (rewrite encBits_tt || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_110_110_D (u : list bool) (r : side) :
  cfgD u ([S0; S1; S1] *> r) -[ tm ]->+ cfgB u ([S1; S0; S0; S1] *> r).
Proof.
  unfold cfgD, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_1001_D (u : list bool) (r : side) :
  cfgD u ([S1; S0; S0; S1] *> r) -[ tm ]->+ cfgD (false :: true :: false :: false :: u) r.
Proof.
  unfold cfgD.
  repeat (rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_1001_A (u : list bool) (r : side) :
  cfgA u ([S1; S0; S0; S1] *> r) -[ tm ]->+ cfgD (true :: false :: false :: u) r.
Proof.
  unfold cfgA, cfgD.
  repeat (rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma box_110_100 (v : list bool) (r : side) :
  cfgB (true :: true :: true :: false :: false :: v) r -[ tm ]->+
  cfgB v ([S1; S0; S1; S0; S0; S1] *> r).
Proof.
  unfold cfgB.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_101001_D (v : list bool) (r : side) :
  cfgD v ([S1; S0; S1; S0; S0; S1] *> r) -[ tm ]->+
  cfgB v ([S1; S0; S0; S0; S0; S0; S1] *> r).
Proof.
  unfold cfgD, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_1000001_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S0; S0; S0; S0; S1] *> r) -[ tm ]->+
  cfgB v ([S1; S0; S0; S0; S1; S0; S1] *> r).
Proof.
  unfold cfgA, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_1000101_D (v : list bool) (r : side) :
  cfgD v ([S1; S0; S0; S0; S1; S0; S1] *> r) -[ tm ]->+
  cfgD (true :: true :: false :: true :: false :: false :: v) r.
Proof.
  unfold cfgD.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_1000101_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S0; S0; S1; S0; S1] *> r) -[ tm ]->+
  cfgD (true :: true :: true :: false :: false :: v) r.
Proof.
  unfold cfgA, cfgD.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_101001_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S1; S0; S0; S1] *> r) -[ tm ]->+
  cfgB v ([S1; S0; S0; S0; S0; S1] *> r).
Proof.
  unfold cfgA, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_100001_D (v : list bool) (r : side) :
  cfgD v ([S1; S0; S0; S0; S0; S1] *> r) -[ tm ]->+
  cfgB v ([S1; S0; S0; S1; S0; S0; S1] *> r).
Proof.
  unfold cfgD, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_100001_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S0; S0; S0; S1] *> r) -[ tm ]->+
  cfgB v ([S1; S0; S0; S0; S1; S1] *> r).
Proof.
  unfold cfgA, cfgB.
  repeat rewrite encBits_f.
  run_steps.
Qed.

Lemma ret_100011_D (v : list bool) (r : side) :
  cfgD v ([S1; S0; S0; S0; S1; S1] *> r) -[ tm ]->+
  cfgA (true :: true :: false :: true :: false :: false :: v) r.
Proof.
  unfold cfgD, cfgA.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

Lemma ret_100011_A (v : list bool) (r : side) :
  cfgA v ([S1; S0; S0; S0; S1; S1] *> r) -[ tm ]->+
  cfgA (true :: true :: true :: false :: false :: v) r.
Proof.
  unfold cfgA.
  repeat (rewrite encBits_tt || rewrite encBits_tf || rewrite encBits_f).
  run_steps.
Qed.

(* ========================================================================== *)
(* Section 4: Finite Block-DFA & Stream-Gap Potential                         *)
(* ========================================================================== *)

Inductive Q5 : Type :=
  | q0
  | qT
  | qTF
  | qFT
  | qFTF.

Fixpoint InL (q : Q5) (xs : list bool) : Prop :=
  match q, xs with
  | q0, [] => True
  | q0, true :: xs' => InL qT xs'
  | q0, false :: xs' => InL qFT xs'
  | qT, true :: xs' => InL q0 xs'
  | qT, false :: xs' => InL qTF xs'
  | qTF, false :: xs' => InL q0 xs'
  | qFT, true :: xs' => InL qFTF xs'
  | qFTF, false :: xs' => InL qTF xs'
  | _, _ => False
  end.

Inductive TokDecomp : list bool -> Prop :=
  | td_emp : TokDecomp []
  | td_w100 (u : list bool) : InL q0 u -> TokDecomp (true :: false :: false :: u)
  | td_w0100 (u : list bool) : InL q0 u -> TokDecomp (false :: true :: false :: false :: u)
  | td_w110 (u : list bool) : InL q0 u -> TokDecomp (true :: true :: u).

Lemma inl_decomp (xs : list bool) (h : InL q0 xs) : TokDecomp xs.
Proof.
  destruct xs as [| [|] [| [|] [| [|] [| [|] u]]]];
    cbn [InL] in h;
    try contradiction;
    constructor; exact h.
Qed.

Definition is110Head (xs : list bool) : bool :=
  match xs with
  | true :: true :: _ => true
  | _ => false
  end.

Fixpoint tokLen (xs : list bool) : nat :=
  match xs with
  | true :: true :: u => tokLen u + 1
  | true :: false :: false :: u => tokLen u + 1
  | false :: true :: false :: false :: u => tokLen u + 1
  | _ => 0
  end.

Lemma tokLen_nil : tokLen [] = 0.
Proof. reflexivity. Qed.

Lemma tokLen_110 (u : list bool) : tokLen (true :: true :: u) = tokLen u + 1.
Proof. reflexivity. Qed.

Lemma tokLen_100 (u : list bool) :
  tokLen (true :: false :: false :: u) = tokLen u + 1.
Proof. reflexivity. Qed.

Lemma tokLen_0100 (u : list bool) :
  tokLen (false :: true :: false :: false :: u) = tokLen u + 1.
Proof. reflexivity. Qed.

Arguments tokLen _ : simpl never.

Definition step110_100 (cv Gv : nat) : option (nat * nat) :=
  match Gv with
  | 0 => None
  | S Gv' =>
    match cv mod 3 with
    | 2 => Some ((cv + 1) / 3, Gv' + 2)
    | 1 => Some (cv / 3, Gv' + 1)
    | _ =>
      if Nat.leb (Gv' + 1) cv then None
      else Some (cv / 3, Gv' / 3)
    end
  end.

Fixpoint potBits (xs : list bool) : option (nat * nat) :=
  match xs with
  | [] => Some (0, 0)
  | true :: false :: false :: u =>
    match potBits u with
    | None => None
    | Some (cu, Gu) => Some (cu + 1, Gu + 1)
    end
  | false :: true :: false :: false :: u =>
    match potBits u with
    | None => None
    | Some (cu, _) => Some (0, cu + 1)
    end
  | true :: true :: u =>
    match u with
    | [] => Some (0, 0)
    | false :: true :: false :: false :: v =>
      match potBits v with
      | None => None
      | Some (cv, _) => Some (0, cv + 1)
      end
    | true :: true :: _ => potBits u
    | true :: false :: false :: v =>
      match potBits v with
      | None => None
      | Some (cv, Gv) => step110_100 cv Gv
      end
    | _ => None
    end
  | _ => None
  end.

Lemma potBits_eq_1 : potBits [] = Some (0, 0).
Proof. reflexivity. Qed.

Lemma potBits_eq_2 (u : list bool) :
  potBits (true :: false :: false :: u) =
  match potBits u with
  | None => None
  | Some (cu, Gu) => Some (cu + 1, Gu + 1)
  end.
Proof. reflexivity. Qed.

Lemma potBits_eq_3 (u : list bool) :
  potBits (false :: true :: false :: false :: u) =
  match potBits u with
  | None => None
  | Some (cu, _) => Some (0, cu + 1)
  end.
Proof. reflexivity. Qed.

Lemma potBits_eq_4 : potBits [true; true] = Some (0, 0).
Proof. reflexivity. Qed.

Lemma potBits_eq_5 (v : list bool) :
  potBits (true :: true :: false :: true :: false :: false :: v) =
  match potBits v with
  | None => None
  | Some (cv, _) => Some (0, cv + 1)
  end.
Proof. reflexivity. Qed.

Lemma potBits_eq_6 (z : list bool) :
  potBits (true :: true :: true :: true :: z) = potBits (true :: true :: z).
Proof. reflexivity. Qed.

Lemma potBits_eq_7 (v : list bool) :
  potBits (true :: true :: true :: false :: false :: v) =
  match potBits v with
  | None => None
  | Some (cv, Gv) => step110_100 cv Gv
  end.
Proof. reflexivity. Qed.

Arguments potBits _ : simpl never.

Lemma potBits_110_of_is110Head {u : list bool}
    (hu : InL q0 u) (hh : is110Head u = true) :
  potBits (true :: true :: u) = potBits u.
Proof.
  destruct (inl_decomp u hu) as [| w _ | w _ | z _].
  - discriminate hh.
  - discriminate hh.
  - discriminate hh.
  - exact (potBits_eq_6 z).
Qed.

Local Arguments Nat.div _ _ : simpl never.
Local Arguments Nat.modulo _ _ : simpl never.

Ltac div3_pose x :=
  pose proof (Nat.div_mod x 3 ltac:(discriminate));
  pose proof (Nat.mod_upper_bound x 3 ltac:(discriminate)).

Lemma step110_100_le {cv Gv c G : nat}
    (hcv : cv <= Gv) (hs : step110_100 cv Gv = Some (c, G)) :
  c <= G.
Proof.
  unfold step110_100 in hs.
  destruct Gv as [| Gv']; [discriminate hs |].
  div3_pose cv; div3_pose (cv + 1); div3_pose Gv'.
  assert (hmod : cv mod 3 = 0 \/ cv mod 3 = 1 \/ cv mod 3 = 2) by lia.
  destruct hmod as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2 in hs.
  - destruct (Nat.leb (Gv' + 1) cv) eqn:hleb; [discriminate hs |].
    apply Nat.leb_gt in hleb.
    injection hs as hc hG. lia.
  - injection hs as hc hG. lia.
  - injection hs as hc hG. lia.
Qed.

Lemma potBits_c_le_G {xs : list bool} {c G : nat}
    (hIn : InL q0 xs) (hpot : potBits xs = Some (c, G)) :
  c <= G.
Proof.
  remember (List.length xs) as n eqn:Hn.
  revert xs c G Hn hIn hpot.
  induction n as [n ih] using strong_induction.
  intros xs c G Hn hIn hpot.
  destruct (inl_decomp xs hIn) as [| u hu | u _ | u hu].
  - rewrite potBits_eq_1 in hpot. injection hpot as hc hG. lia.
  - rewrite potBits_eq_2 in hpot.
    destruct (potBits u) as [[cu Gu] |] eqn:hpu; [| discriminate hpot].
    injection hpot as hc hG.
    assert (hle : cu <= Gu).
    { apply (ih (List.length u) ltac:(cbn [List.length] in Hn; lia) u cu Gu eq_refl hu hpu). }
    lia.
  - rewrite potBits_eq_3 in hpot.
    destruct (potBits u) as [[cu Gu] |] eqn:hpu; [| discriminate hpot].
    injection hpot as hc hG. lia.
  - destruct (inl_decomp u hu) as [| v hv | v _ | z _].
    + rewrite potBits_eq_4 in hpot. injection hpot as hc hG. lia.
    + rewrite potBits_eq_7 in hpot.
      destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
      assert (hle : cv <= Gv).
      { apply (ih (List.length v) ltac:(cbn [List.length] in Hn; lia) v cv Gv eq_refl hv hpv). }
      exact (step110_100_le hle hpot).
    + rewrite potBits_eq_5 in hpot.
      destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
      injection hpot as hc hG. lia.
    + rewrite potBits_eq_6 in hpot.
      exact (ih (List.length (true :: true :: z))
                ltac:(cbn [List.length] in Hn |- *; lia)
                (true :: true :: z) c G eq_refl hu hpot).
Qed.

Lemma step110_100_succ3 {cv Gv c G Gv3 : nat}
    (hs : step110_100 (cv + 3) Gv = Some (c + 1, G))
    (hG : Gv <= Gv3) :
  exists G1, step110_100 cv Gv3 = Some (c, G1) /\ G <= G1.
Proof.
  unfold step110_100 in hs |- *.
  destruct Gv as [| Gv']; [discriminate hs |].
  destruct Gv3 as [| Gv3']; [lia |].
  div3_pose cv; div3_pose (cv + 3); div3_pose (cv + 1); div3_pose (cv + 3 + 1);
  div3_pose Gv'; div3_pose Gv3'.
  assert (hmod_eq : (cv + 3) mod 3 = cv mod 3) by lia.
  rewrite hmod_eq in hs.
  assert (hmod : cv mod 3 = 0 \/ cv mod 3 = 1 \/ cv mod 3 = 2) by lia.
  destruct hmod as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2 in hs |- *.
  - destruct (Nat.leb (Gv' + 1) (cv + 3)) eqn:hleb; [discriminate hs |].
    apply Nat.leb_gt in hleb.
    injection hs as hc hG0.
    destruct (Nat.leb (Gv3' + 1) cv) eqn:hleb2.
    + apply Nat.leb_le in hleb2. lia.
    + exists (Gv3' / 3).
      replace (cv / 3) with c by lia.
      split; [reflexivity | lia].
  - injection hs as hc hG0.
    exists (Gv3' + 1).
    replace (cv / 3) with c by lia.
    split; [reflexivity | lia].
  - injection hs as hc hG0.
    exists (Gv3' + 2).
    replace ((cv + 1) / 3) with c by lia.
    split; [reflexivity | lia].
Qed.

Lemma step110_100_c0_preserve {Gv' c2 Gv3 : nat}
    (hc2 : Gv' <= c2 + 1) (hG : Gv' + 1 <= Gv3) (hlt : c2 < Gv3) :
  exists c_out G_out,
    step110_100 c2 Gv3 = Some (c_out, G_out) /\
    Gv' / 3 <= c_out /\ Gv' / 3 <= G_out.
Proof.
  unfold step110_100.
  destruct Gv3 as [| Gv3']; [lia |].
  div3_pose c2; div3_pose (c2 + 1); div3_pose Gv'; div3_pose Gv3'.
  assert (hmod : c2 mod 3 = 0 \/ c2 mod 3 = 1 \/ c2 mod 3 = 2) by lia.
  destruct hmod as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2.
  - destruct (Nat.leb (Gv3' + 1) c2) eqn:hleb.
    + apply Nat.leb_le in hleb. lia.
    + exists (c2 / 3), (Gv3' / 3).
      split; [reflexivity | split; lia].
  - exists (c2 / 3), (Gv3' + 1).
    split; [reflexivity | split; lia].
  - exists ((c2 + 1) / 3), (Gv3' + 2).
    split; [reflexivity | split; lia].
Qed.

Lemma step110_100_c0_inv {cv Gv G : nat}
    (hs : step110_100 cv Gv = Some (0, G)) :
  exists Gv', Gv = S Gv' /\ ((cv = 0 /\ G = Gv' / 3) \/ (cv = 1 /\ G = Gv' + 1)).
Proof.
  unfold step110_100 in hs.
  destruct Gv as [| Gv']; [discriminate hs |].
  exists Gv'. split; [reflexivity |].
  destruct cv as [| [| cv1]].
  - change (0 mod 3) with 0 in hs. change (0 / 3) with 0 in hs.
    destruct (Nat.leb (Gv' + 1) 0) eqn:hleb; [discriminate hs |].
    injection hs as hG. left. split; [reflexivity | symmetry; exact hG].
  - change (1 mod 3) with 1 in hs. change (1 / 3) with 0 in hs.
    injection hs as hG. right. split; [reflexivity | symmetry; exact hG].
  - exfalso.
    remember (S (S cv1)) as x eqn:hx.
    div3_pose x; div3_pose (x + 1).
    assert (hmod : x mod 3 = 0 \/ x mod 3 = 1 \/ x mod 3 = 2) by lia.
    destruct hmod as [h0 | [h1 | h2]]; rewrite ?h0, ?h1, ?h2 in hs.
    + destruct (Nat.leb (Gv' + 1) x); [discriminate hs |].
      injection hs as hc _. lia.
    + injection hs as hc _. lia.
    + injection hs as hc _. lia.
Qed.

Lemma step110_100_cS_inv {cv Gv c' G : nat}
    (hs : step110_100 cv Gv = Some (c' + 1, G)) :
  (cv = 2 /\ c' = 0 /\ exists Gv', Gv = S Gv' /\ G = Gv' + 2) \/
  (exists cv3, cv = cv3 + 3).
Proof.
  destruct cv as [| [| [| cv3]]].
  - exfalso. unfold step110_100 in hs.
    destruct Gv as [| Gv']; [discriminate hs |].
    change (0 mod 3) with 0 in hs. change (0 / 3) with 0 in hs.
    destruct (Nat.leb (Gv' + 1) 0); [discriminate hs |].
    injection hs as hc _. lia.
  - exfalso. unfold step110_100 in hs.
    destruct Gv as [| Gv']; [discriminate hs |].
    change (1 mod 3) with 1 in hs. change (1 / 3) with 0 in hs.
    injection hs as hc _. lia.
  - left. unfold step110_100 in hs.
    destruct Gv as [| Gv']; [discriminate hs |].
    change (2 mod 3) with 2 in hs. change ((2 + 1) / 3) with 1 in hs.
    injection hs as hc hG.
    split; [reflexivity | split; [lia | exists Gv'; split; [reflexivity | lia]]].
  - right. exists cv3. lia.
Qed.

Lemma push110_potBits {xs1 : list bool} {c' G1 : nat}
    (hIn : InL q0 xs1) (hpot : potBits xs1 = Some (c', G1)) (hG : c' + 1 <= G1) :
  exists c2 G2, potBits (true :: true :: xs1) = Some (c2, G2).
Proof.
  destruct (inl_decomp xs1 hIn) as [| v hv | v _ | z _].
  - exists 0, 0. exact potBits_eq_4.
  - rewrite potBits_eq_2 in hpot.
    destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
    injection hpot as hc hG1.
    destruct (@step110_100_c0_preserve 0 cv Gv ltac:(lia) ltac:(lia) ltac:(lia))
      as [c2 [G2 [hs _]]].
    exists c2, G2.
    rewrite potBits_eq_7, hpv. exact hs.
  - rewrite potBits_eq_3 in hpot.
    destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
    exists 0, (cv + 1).
    rewrite potBits_eq_5, hpv. reflexivity.
  - exists c', G1.
    rewrite potBits_eq_6. exact hpot.
Qed.

(* ========================================================================== *)
(* Section 5: Step-Indexed CPS Safety Contracts (BoxCPS & top_safe)           *)
(* ========================================================================== *)

Definition BoxCPS_D (n : nat) (xs : list bool) (G : nat) : Prop :=
  forall (k : nat) (r : side),
    (forall (j : nat) (xs1 : list bool) (c1 G1 : nat),
      j < k -> tokLen xs1 = n -> InL q0 xs1 -> potBits xs1 = Some (c1, G1) ->
      G <= c1 -> G <= G1 -> Safe j (cfgD xs1 r)) ->
    Safe k (cfgB xs r).

Definition BoxCPS_A (n : nat) (xs : list bool) (c' G : nat) : Prop :=
  forall (k : nat) (r : side),
    (forall (j : nat) (xs1 : list bool) (G1 : nat),
      j < k -> tokLen xs1 = n -> InL q0 xs1 -> potBits xs1 = Some (c', G1) ->
      G <= G1 -> (is110Head xs = true -> is110Head xs1 = true) ->
      Safe j (cfgA xs1 r)) ->
    Safe k (cfgB xs r).

Definition BoxCPS_at (n : nat) (xs : list bool) (c G : nat) : Prop :=
  (c = 0 -> BoxCPS_D n xs G) /\
  (forall c', c = c' + 1 -> BoxCPS_A n xs c' G).

Definition BoxCPS (n : nat) : Prop :=
  forall (xs : list bool) (c G : nat),
    tokLen xs = n ->
    InL q0 xs ->
    potBits xs = Some (c, G) ->
    BoxCPS_at n xs c G.

Lemma box_cps_emp (n c G : nat)
    (hlen : tokLen [] = n)
    (hpot : potBits [] = Some (c, G)) :
  BoxCPS_at n [] c G.
Proof.
  rewrite potBits_eq_1 in hpot.
  injection hpot as hc hG. subst c G.
  split; [intros _ k r hcont | intros c' hc'; lia].
  eapply Safe_of_stepPlus; [exact (box_emp r) | intros k' hk'].
  exact (hcont k' [] 0 0 hk' hlen I potBits_eq_1 (Nat.le_refl 0) (Nat.le_refl 0)).
Qed.

Lemma box_cps_w0100 (n : nat) (u : list bool) (c G : nat)
    (hlen : tokLen (false :: true :: false :: false :: u) = n)
    (hu : InL q0 u)
    (hpot : potBits (false :: true :: false :: false :: u) = Some (c, G)) :
  BoxCPS_at n (false :: true :: false :: false :: u) c G.
Proof.
  rewrite potBits_eq_3 in hpot.
  destruct (potBits u) as [[cu Gu] |] eqn:hpu; [| discriminate hpot].
  injection hpot as hc hG. subst c G.
  pose proof (potBits_c_le_G hu hpu) as hu_le.
  split; [intros _ k r hcont | intros c' hc'; lia].
  eapply Safe_of_stepPlus; [exact (box_0100 u r) | intros k' hk'].
  assert (hp_out : potBits (true :: false :: false :: u) = Some (cu + 1, Gu + 1))
    by (rewrite potBits_eq_2, hpu; reflexivity).
  assert (hl_out : tokLen (true :: false :: false :: u) = n)
    by (rewrite tokLen_0100 in hlen; rewrite tokLen_100; exact hlen).
  exact (hcont k' (true :: false :: false :: u) (cu + 1) (Gu + 1)
               hk' hl_out hu hp_out (Nat.le_refl _) ltac:(lia)).
Qed.

Lemma box_cps_w100 (n : nat) (ih : forall m, m < n -> BoxCPS m)
    (u : list bool) (c G : nat)
    (hlen : tokLen (true :: false :: false :: u) = n)
    (hu : InL q0 u)
    (hpot : potBits (true :: false :: false :: u) = Some (c, G)) :
  BoxCPS_at n (true :: false :: false :: u) c G.
Proof.
  rewrite potBits_eq_2 in hpot.
  destruct (potBits u) as [[cu Gu] |] eqn:hpu; [| discriminate hpot].
  injection hpot as hc hG. subst c G.
  rewrite tokLen_100 in hlen.
  pose proof (ih (tokLen u) ltac:(lia) u cu Gu eq_refl hu hpu) as [ih_D ih_A].
  split; [intros hc; lia | intros c' hc' k r hcont].
  assert (hc_eq : c' = cu) by lia. subst c'.
  eapply Safe_of_stepPlus; [exact (box_100 u r) | intros k1 hk1].
  destruct cu as [| c''].
  - apply (ih_D eq_refl k1 ([S1; S0; S0] *> r)).
    intros k2 u1 c1 G1 hk2 hlu1 hu1 hpu1 hGc _.
    eapply Safe_of_stepPlus; [exact (ret_100_D u1 r) | intros k3 hk3].
    assert (hp_out : potBits (false :: true :: false :: false :: u1) = Some (0, c1 + 1))
      by (rewrite potBits_eq_3, hpu1; reflexivity).
    assert (hl_out : tokLen (false :: true :: false :: false :: u1) = n)
      by (rewrite tokLen_0100; lia).
    exact (hcont k3 (false :: true :: false :: false :: u1) (c1 + 1)
                 ltac:(lia) hl_out hu1 hp_out ltac:(lia)
                 (fun hh => ltac:(discriminate hh))).
  - apply (ih_A c'' ltac:(lia) k1 ([S1; S0; S0] *> r)).
    intros k2 u1 G1 hk2 hlu1 hu1 hpu1 hGG _.
    eapply Safe_of_stepPlus; [exact (ret_100_A u1 r) | intros k3 hk3].
    assert (hp_out : potBits (true :: false :: false :: u1) = Some (S c'', G1 + 1))
      by (rewrite potBits_eq_2, hpu1; f_equal; f_equal; lia).
    assert (hl_out : tokLen (true :: false :: false :: u1) = n)
      by (rewrite tokLen_100; lia).
    exact (hcont k3 (true :: false :: false :: u1) (G1 + 1)
                 ltac:(lia) hl_out hu1 hp_out ltac:(lia)
                 (fun hh => ltac:(discriminate hh))).
Qed.

Lemma box_cps_w110_emp (n c G : nat)
    (hlen : tokLen [true; true] = n)
    (hpot : potBits [true; true] = Some (c, G)) :
  BoxCPS_at n [true; true] c G.
Proof.
  rewrite potBits_eq_4 in hpot.
  injection hpot as hc hG. subst c G.
  split; [intros _ k r hcont | intros c' hc'; lia].
  eapply Safe_of_stepPlus; [exact (box_110_emp r) | intros k' hk'].
  assert (hp0100 : potBits [false; true; false; false] = Some (0, 1))
    by (rewrite potBits_eq_3, potBits_eq_1; reflexivity).
  assert (hl0100 : tokLen [false; true; false; false] = n)
    by (rewrite tokLen_110, tokLen_nil in hlen; rewrite tokLen_0100, tokLen_nil; exact hlen).
  exact (hcont k' [false; true; false; false] 0 1
               hk' hl0100 I hp0100 (Nat.le_0_l 0) (Nat.le_0_l 1)).
Qed.

Lemma box_cps_w110_w0100 (n : nat) (ih : forall m, m < n -> BoxCPS m)
    (v : list bool) (c G : nat)
    (hlen : tokLen (true :: true :: false :: true :: false :: false :: v) = n)
    (hv : InL q0 v)
    (hpot : potBits (true :: true :: false :: true :: false :: false :: v) = Some (c, G)) :
  BoxCPS_at n (true :: true :: false :: true :: false :: false :: v) c G.
Proof.
  rewrite potBits_eq_5 in hpot.
  destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
  injection hpot as hc hG. subst c G.
  rewrite tokLen_110, tokLen_0100 in hlen.
  pose proof (ih (tokLen v) ltac:(lia) v cv Gv eq_refl hv hpv) as [ih_D ih_A].
  split; [intros _ k r hcont | intros c' hc'; lia].
  eapply Safe_of_stepPlus; [exact (box_110_0100 v r) | intros k1 hk1].
  destruct cv as [| cv'].
  - apply (ih_D eq_refl k1 ([S1; S0; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 c1 G1 hk2 hlv1 hv1 hpv1 _ _.
    eapply Safe_of_stepPlus; [exact (ret_110_0100_D v1 r) | intros k3 hk3].
    assert (hp_out : potBits (true :: false :: false :: false :: true :: false :: false :: v1) =
                     Some (1, c1 + 2))
      by (rewrite potBits_eq_2, potBits_eq_3, hpv1; f_equal; f_equal; lia).
    assert (hl_out : tokLen (true :: false :: false :: false :: true :: false :: false :: v1) = n)
      by (rewrite tokLen_100, tokLen_0100; lia).
    exact (hcont k3 (true :: false :: false :: false :: true :: false :: false :: v1)
                 1 (c1 + 2) ltac:(lia) hl_out hv1 hp_out ltac:(lia) ltac:(lia)).
  - pose proof (potBits_c_le_G hv hpv) as hcv_le.
    apply (ih_A cv' ltac:(lia) k1 ([S1; S0; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 G1 hk2 hlv1 hv1 hpv1 hGG _.
    eapply Safe_of_stepPlus; [exact (ret_110_0100_A v1 r) | intros k3 hk3].
    assert (hp_out : potBits (true :: false :: false :: true :: false :: false :: v1) =
                     Some (cv' + 2, G1 + 2))
      by (rewrite potBits_eq_2, potBits_eq_2, hpv1; f_equal; f_equal; lia).
    assert (hl_out : tokLen (true :: false :: false :: true :: false :: false :: v1) = n)
      by (rewrite tokLen_100, tokLen_100; lia).
    exact (hcont k3 (true :: false :: false :: true :: false :: false :: v1)
                 (cv' + 2) (G1 + 2) ltac:(lia) hl_out hv1 hp_out ltac:(lia) ltac:(lia)).
Qed.

Lemma box_cps_w110_w110 (n : nat) (ih : forall m, m < n -> BoxCPS m)
    (z : list bool) (c G : nat)
    (hlen : tokLen (true :: true :: true :: true :: z) = n)
    (hu : InL q0 (true :: true :: z))
    (hpot : potBits (true :: true :: true :: true :: z) = Some (c, G)) :
  BoxCPS_at n (true :: true :: true :: true :: z) c G.
Proof.
  rewrite potBits_eq_6 in hpot.
  rewrite tokLen_110 in hlen.
  pose proof (ih (tokLen (true :: true :: z)) ltac:(lia) (true :: true :: z) c G eq_refl hu hpot)
    as [ih_D ih_A].
  split.
  - intros hc k r hcont. subst c.
    eapply Safe_of_stepPlus; [exact (box_110_110 z r) | intros k1 hk1].
    apply (ih_D eq_refl k1 ([S0; S1; S1] *> r)).
    intros k2 u1 c1 G1 hk2 hlu1 hu1 hpu1 hGc1 hGG1.
    eapply Safe_of_stepPlus; [exact (ret_110_110_D u1 r) | intros k3 hk3].
    pose proof (ih (tokLen u1) ltac:(lia) u1 c1 G1 eq_refl hu1 hpu1) as [ih1_D ih1_A].
    destruct c1 as [| c1'].
    + apply (ih1_D eq_refl k3 ([S1; S0; S0; S1] *> r)).
      intros k4 u2 c2 G2 hk4 hlu2 hu2 hpu2 _ _.
      eapply Safe_of_stepPlus; [exact (ret_1001_D u2 r) | intros k5 hk5].
      assert (hp_out : potBits (false :: true :: false :: false :: u2) = Some (0, c2 + 1))
        by (rewrite potBits_eq_3, hpu2; reflexivity).
      assert (hl_out : tokLen (false :: true :: false :: false :: u2) = n)
        by (rewrite tokLen_0100; lia).
      exact (hcont k5 (false :: true :: false :: false :: u2) 0 (c2 + 1)
                   ltac:(lia) hl_out hu2 hp_out ltac:(lia) ltac:(lia)).
    + apply (ih1_A c1' ltac:(lia) k3 ([S1; S0; S0; S1] *> r)).
      intros k4 u2 G2 hk4 hlu2 hu2 hpu2 hGG2 _.
      eapply Safe_of_stepPlus; [exact (ret_1001_A u2 r) | intros k5 hk5].
      assert (hp_out : potBits (true :: false :: false :: u2) = Some (c1' + 1, G2 + 1))
        by (rewrite potBits_eq_2, hpu2; reflexivity).
      assert (hl_out : tokLen (true :: false :: false :: u2) = n)
        by (rewrite tokLen_100; lia).
      exact (hcont k5 (true :: false :: false :: u2) (c1' + 1) (G2 + 1)
                   ltac:(lia) hl_out hu2 hp_out ltac:(lia) ltac:(lia)).
  - intros c' hc' k r hcont.
    eapply Safe_of_stepPlus; [exact (box_110_110 z r) | intros k1 hk1].
    apply (ih_A c' hc' k1 ([S0; S1; S1] *> r)).
    intros k2 u1 G1 hk2 hlu1 hu1 hpu1 hGG1 hh1.
    eapply Safe_of_stepPlus; [exact (ret_110_110_A u1 r) | intros k3 hk3].
    assert (hh_u1 : is110Head u1 = true) by exact (hh1 eq_refl).
    assert (hp_out : potBits (true :: true :: u1) = Some (c', G1))
      by (rewrite (potBits_110_of_is110Head hu1 hh_u1); exact hpu1).
    assert (hl_out : tokLen (true :: true :: u1) = n)
      by (rewrite tokLen_110; lia).
    exact (hcont k3 (true :: true :: u1) G1
                 ltac:(lia) hl_out hu1 hp_out hGG1 (fun _ => eq_refl)).
Qed.

Lemma box_cps_w110_w100_c0 (n : nat) (ih : forall m, m < n -> BoxCPS m)
    (v : list bool) (cv Gv G : nat)
    (hlen : tokLen v + 2 = n)
    (hv : InL q0 v)
    (hpv : potBits v = Some (cv, Gv))
    (hpot : step110_100 cv Gv = Some (0, G)) :
  BoxCPS_D n (true :: true :: true :: false :: false :: v) G.
Proof.
  pose proof (potBits_c_le_G hv hpv) as hcv_le.
  destruct (step110_100_c0_inv hpot) as [Gv' [-> [[-> ->] | [-> ->]]]].
  - intros k r hcont.
    pose proof (ih (tokLen v) ltac:(lia) v 0 (S Gv') eq_refl hv hpv) as [ih_v_D _].
    eapply Safe_of_stepPlus; [exact (box_110_100 v r) | intros k1 hk1].
    apply (ih_v_D eq_refl k1 ([S1; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 c1 G1 hk2 hlv1 hv1 hpv1 hGc1 hGG1.
    eapply Safe_of_stepPlus; [exact (ret_101001_D v1 r) | intros k3 hk3].
    destruct c1 as [| c1']; [lia |].
    pose proof (ih (tokLen v1) ltac:(lia) v1 (S c1') G1 eq_refl hv1 hpv1) as [_ ih_v1_A].
    apply (ih_v1_A c1' ltac:(lia) k3 ([S1; S0; S0; S0; S0; S0; S1] *> r)).
    intros k4 v2 G2 hk4 hlv2 hv2 hpv2 hGG2 _.
    eapply Safe_of_stepPlus; [exact (ret_1000001_A v2 r) | intros k5 hk5].
    pose proof (potBits_c_le_G hv1 hpv1) as hc1_le_G1.
    pose proof (ih (tokLen v2) ltac:(lia) v2 c1' G2 eq_refl hv2 hpv2) as [ih_v2_D ih_v2_A].
    destruct c1' as [| c2].
    + div3_pose Gv'.
      assert (hGv_div : Gv' / 3 = 0) by lia.
      apply (ih_v2_D eq_refl k5 ([S1; S0; S0; S0; S1; S0; S1] *> r)).
      intros k6 v3 c3 G3 hk6 hlv3 hv3 hpv3 _ _.
      eapply Safe_of_stepPlus; [exact (ret_1000101_D v3 r) | intros k7 hk7].
      assert (hp_out : potBits (true :: true :: false :: true :: false :: false :: v3) =
                       Some (0, c3 + 1))
        by (rewrite potBits_eq_5, hpv3; reflexivity).
      assert (hl_out : tokLen (true :: true :: false :: true :: false :: false :: v3) = n)
        by (rewrite tokLen_110, tokLen_0100; lia).
      exact (hcont k7 (true :: true :: false :: true :: false :: false :: v3)
                   0 (c3 + 1) ltac:(lia) hl_out hv3 hp_out ltac:(lia) ltac:(lia)).
    + apply (ih_v2_A c2 ltac:(lia) k5 ([S1; S0; S0; S0; S1; S0; S1] *> r)).
      intros k6 v3 G3 hk6 hlv3 hv3 hpv3 hGG3 _.
      eapply Safe_of_stepPlus; [exact (ret_1000101_A v3 r) | intros k7 hk7].
      destruct (@step110_100_c0_preserve Gv' c2 G3 ltac:(lia) ltac:(lia) ltac:(lia))
        as [c_out [G_out [hs_out [hc_ge hG_ge]]]].
      assert (hp_out : potBits (true :: true :: true :: false :: false :: v3) =
                       Some (c_out, G_out))
        by (rewrite potBits_eq_7, hpv3; exact hs_out).
      assert (hl_out : tokLen (true :: true :: true :: false :: false :: v3) = n)
        by (rewrite tokLen_110, tokLen_100; lia).
      exact (hcont k7 (true :: true :: true :: false :: false :: v3)
                   c_out G_out ltac:(lia) hl_out hv3 hp_out hc_ge hG_ge).
  - intros k r hcont.
    pose proof (ih (tokLen v) ltac:(lia) v 1 (S Gv') eq_refl hv hpv) as [_ ih_v_A].
    eapply Safe_of_stepPlus; [exact (box_110_100 v r) | intros k1 hk1].
    apply (ih_v_A 0 eq_refl k1 ([S1; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 G1 hk2 hlv1 hv1 hpv1 hGG1 _.
    eapply Safe_of_stepPlus; [exact (ret_101001_A v1 r) | intros k3 hk3].
    pose proof (ih (tokLen v1) ltac:(lia) v1 0 G1 eq_refl hv1 hpv1) as [ih_v1_D _].
    apply (ih_v1_D eq_refl k3 ([S1; S0; S0; S0; S0; S1] *> r)).
    intros k4 v2 c2 G2 hk4 hlv2 hv2 hpv2 hGc2 hGG2.
    eapply Safe_of_stepPlus; [exact (ret_100001_D v2 r) | intros k5 hk5].
    destruct c2 as [| c2']; [lia |].
    pose proof (ih (tokLen v2) ltac:(lia) v2 (S c2') G2 eq_refl hv2 hpv2) as [_ ih_v2_A].
    apply (ih_v2_A c2' ltac:(lia) k5 ([S1; S0; S0; S1; S0; S0; S1] *> r)).
    intros k6 v3 G3 hk6 hlv3 hv3 hpv3 hGG3 _.
    eapply Safe_of_stepPlus; [exact (ret_110_0100_A v3 r) | intros k7 hk7].
    assert (hp_out : potBits (true :: false :: false :: true :: false :: false :: v3) =
                     Some (c2' + 2, G3 + 2))
      by (rewrite potBits_eq_2, potBits_eq_2, hpv3; f_equal; f_equal; lia).
    assert (hl_out : tokLen (true :: false :: false :: true :: false :: false :: v3) = n)
      by (rewrite tokLen_100, tokLen_100; lia).
    exact (hcont k7 (true :: false :: false :: true :: false :: false :: v3)
                 (c2' + 2) (G3 + 2) ltac:(lia) hl_out hv3 hp_out ltac:(lia) ltac:(lia)).
Qed.

Lemma box_cps_w110_w100_cS (n : nat) (ih : forall m, m < n -> BoxCPS m)
    (v : list bool) (cv Gv c' G : nat)
    (hlen : tokLen v + 2 = n)
    (hv : InL q0 v)
    (hpv : potBits v = Some (cv, Gv))
    (hpot : step110_100 cv Gv = Some (c' + 1, G)) :
  BoxCPS_A n (true :: true :: true :: false :: false :: v) c' G.
Proof.
  destruct (step110_100_cS_inv hpot) as [[-> [-> [Gv' [-> ->]]]] | [cv3 ->]].
  - intros k r hcont.
    pose proof (ih (tokLen v) ltac:(lia) v 2 (S Gv') eq_refl hv hpv) as [_ ih_v_A].
    eapply Safe_of_stepPlus; [exact (box_110_100 v r) | intros k1 hk1].
    apply (ih_v_A 1 eq_refl k1 ([S1; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 G1 hk2 hlv1 hv1 hpv1 hGG1 _.
    eapply Safe_of_stepPlus; [exact (ret_101001_A v1 r) | intros k3 hk3].
    pose proof (ih (tokLen v1) ltac:(lia) v1 1 G1 eq_refl hv1 hpv1) as [_ ih_v1_A].
    apply (ih_v1_A 0 eq_refl k3 ([S1; S0; S0; S0; S0; S1] *> r)).
    intros k4 v2 G2 hk4 hlv2 hv2 hpv2 hGG2 _.
    eapply Safe_of_stepPlus; [exact (ret_100001_A v2 r) | intros k5 hk5].
    pose proof (ih (tokLen v2) ltac:(lia) v2 0 G2 eq_refl hv2 hpv2) as [ih_v2_D _].
    apply (ih_v2_D eq_refl k5 ([S1; S0; S0; S0; S1; S1] *> r)).
    intros k6 v3 c3 G3 hk6 hlv3 hv3 hpv3 hGc3 _.
    eapply Safe_of_stepPlus; [exact (ret_100011_D v3 r) | intros k7 hk7].
    assert (hp_out : potBits (true :: true :: false :: true :: false :: false :: v3) =
                     Some (0, c3 + 1))
      by (rewrite potBits_eq_5, hpv3; reflexivity).
    assert (hl_out : tokLen (true :: true :: false :: true :: false :: false :: v3) = n)
      by (rewrite tokLen_110, tokLen_0100; lia).
    exact (hcont k7 (true :: true :: false :: true :: false :: false :: v3)
                 (c3 + 1) ltac:(lia) hl_out hv3 hp_out ltac:(lia) (fun _ => eq_refl)).
  - intros k r hcont.
    pose proof (ih (tokLen v) ltac:(lia) v (cv3 + 3) Gv eq_refl hv hpv) as [_ ih_v_A].
    eapply Safe_of_stepPlus; [exact (box_110_100 v r) | intros k1 hk1].
    apply (ih_v_A (cv3 + 2) ltac:(lia) k1 ([S1; S0; S1; S0; S0; S1] *> r)).
    intros k2 v1 G1 hk2 hlv1 hv1 hpv1 hGG1 _.
    eapply Safe_of_stepPlus; [exact (ret_101001_A v1 r) | intros k3 hk3].
    pose proof (ih (tokLen v1) ltac:(lia) v1 (cv3 + 2) G1 eq_refl hv1 hpv1) as [_ ih_v1_A].
    apply (ih_v1_A (cv3 + 1) ltac:(lia) k3 ([S1; S0; S0; S0; S0; S1] *> r)).
    intros k4 v2 G2 hk4 hlv2 hv2 hpv2 hGG2 _.
    eapply Safe_of_stepPlus; [exact (ret_100001_A v2 r) | intros k5 hk5].
    pose proof (ih (tokLen v2) ltac:(lia) v2 (cv3 + 1) G2 eq_refl hv2 hpv2) as [_ ih_v2_A].
    apply (ih_v2_A cv3 ltac:(lia) k5 ([S1; S0; S0; S0; S1; S1] *> r)).
    intros k6 v3 G3 hk6 hlv3 hv3 hpv3 hGG3 _.
    eapply Safe_of_stepPlus; [exact (ret_100011_A v3 r) | intros k7 hk7].
    destruct (@step110_100_succ3 cv3 Gv c' G G3 hpot ltac:(lia))
      as [G_out [hs_out hG_ge]].
    assert (hp_out : potBits (true :: true :: true :: false :: false :: v3) =
                     Some (c', G_out))
      by (rewrite potBits_eq_7, hpv3; exact hs_out).
    assert (hl_out : tokLen (true :: true :: true :: false :: false :: v3) = n)
      by (rewrite tokLen_110, tokLen_100; lia).
    exact (hcont k7 (true :: true :: true :: false :: false :: v3)
                 G_out ltac:(lia) hl_out hv3 hp_out hG_ge (fun _ => eq_refl)).
Qed.

Theorem box_cps_holds (n : nat) : BoxCPS n.
Proof.
  induction n as [n ih] using strong_induction.
  intros xs c G hlen hIn hpot.
  destruct (inl_decomp xs hIn) as [| u hu | u hu | u hu].
  - exact (box_cps_emp n c G hlen hpot).
  - exact (box_cps_w100 n ih u c G hlen hu hpot).
  - exact (box_cps_w0100 n u c G hlen hu hpot).
  - destruct (inl_decomp u hu) as [| v hv | v hv | z _].
    + exact (box_cps_w110_emp n c G hlen hpot).
    + rewrite potBits_eq_7 in hpot.
      destruct (potBits v) as [[cv Gv] |] eqn:hpv; [| discriminate hpot].
      assert (hlv : tokLen v + 2 = n)
        by (rewrite tokLen_110, tokLen_100 in hlen; lia).
      split.
      * intros hc. subst c.
        exact (box_cps_w110_w100_c0 n ih v cv Gv G hlv hv hpv hpot).
      * intros c' hc'. subst c.
        exact (box_cps_w110_w100_cS n ih v cv Gv c' G hlv hv hpv hpot).
    + exact (box_cps_w110_w0100 n ih v c G hlen hv hpot).
    + exact (box_cps_w110_w110 n ih z c G hlen hu hpot).
Qed.

Theorem top_safe (k : nat) :
  forall (xs : list bool) (c G : nat),
    InL q0 xs -> potBits xs = Some (c, G) -> Safe k (cfgTop xs).
Proof.
  induction k as [k ih] using strong_induction.
  intros xs c G hIn hpot.
  pose proof (potBits_c_le_G hIn hpot) as hcG.
  pose proof (box_cps_holds (tokLen xs) xs c G eq_refl hIn hpot) as [hbox_D hbox_A].
  eapply Safe_of_stepPlus; [exact (top_enter xs) | intros k1 hk1].
  destruct c as [| c'].
  - apply (hbox_D eq_refl k1 ([S0; S1] *> 0inf)).
    intros k2 xs1 c1 G1 hk2 _ hIn1 hpot1 _ _.
    eapply Safe_of_stepPlus; [exact (top_ret_D xs1) | intros k3 hk3].
    pose proof (box_cps_holds (tokLen xs1) xs1 c1 G1 eq_refl hIn1 hpot1)
      as [hbox1_D hbox1_A].
    destruct c1 as [| c1'].
    + apply (hbox1_D eq_refl k3 ([S1] *> 0inf)).
      intros k4 xs2 c2 G2 hk4 _ hIn2 hpot2 _ _.
      eapply Safe_of_stepPlus; [exact (top_ret_DD xs2) | intros k5 hk5].
      assert (hp_out : potBits (false :: true :: false :: false :: xs2) = Some (0, c2 + 1))
        by (rewrite potBits_eq_3, hpot2; reflexivity).
      exact (ih k5 ltac:(lia) (false :: true :: false :: false :: xs2)
                0 (c2 + 1) hIn2 hp_out).
    + apply (hbox1_A c1' ltac:(lia) k3 ([S1] *> 0inf)).
      intros k4 xs2 G2 hk4 _ hIn2 hpot2 _ _.
      eapply Safe_of_stepPlus; [exact (top_ret_DA xs2) | intros k5 hk5].
      assert (hp_out : potBits (true :: false :: false :: xs2) = Some (c1' + 1, G2 + 1))
        by (rewrite potBits_eq_2, hpot2; reflexivity).
      exact (ih k5 ltac:(lia) (true :: false :: false :: xs2)
                (c1' + 1) (G2 + 1) hIn2 hp_out).
  - apply (hbox_A c' ltac:(lia) k1 ([S0; S1] *> 0inf)).
    intros k2 xs1 G1 hk2 _ hIn1 hpot1 hGG1 _.
    eapply Safe_of_stepPlus; [exact (top_ret_A xs1) | intros k3 hk3].
    destruct (push110_potBits hIn1 hpot1 ltac:(lia)) as [c2 [G2 hp_out]].
    exact (ih k3 ltac:(lia) (true :: true :: xs1) c2 G2 hIn1 hp_out).
Qed.

Theorem nonhalt_internal : ~ halts tm c0.
Proof.
  eapply nonhalt_of_forall_safe.
  - exact init_to_top.
  - intro k. exact (top_safe k [] 0 0 I potBits_eq_1).
Qed.

End Internal.

Theorem nonhalt : ~ halts tm c0.
Proof. exact Internal.nonhalt_internal. Qed.
