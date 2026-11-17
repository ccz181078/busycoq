(* 1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC--- halts (BB(6) holdout 608:#339 / 797:#449). *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN NArith PArith PeanoNat Bool String List Lists.Streams.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := TM_from_str "1RB0LE_1RC1RB_1LD0RE_1LA1LC_1RB0LF_0LC---".

Module M339.

Local Open Scope list_scope.
Local Open Scope N_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation "c --> c'" := (c -[ tm ]-> c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Lemma evstep_halts (c c' : Q * tape) :
  c -->* c' -> halts tm c' -> halts tm c.
Proof.
  intros Hreach Hh.
  destruct (with_counter Hreach) as [n Hn].
  eapply halts_multistep; eauto.
Qed.

Lemma N_b2n_odd_mod2 (a : N) : N.b2n (N.odd a) = a mod 2.
Proof.
  rewrite <- N.bit0_mod, N.bit0_odd. reflexivity.
Qed.

(* ========================================================================== *)
(* Section 1: Words, Macros, and Base + Extra Micro-Rules                     *)
(* ========================================================================== *)

Definition npow {A : Type} (u : list A) (n : N) : list A :=
  u ^^ (N.to_nat n).

Arguments npow {A} u n : simpl never.

Lemma npow_0 {A : Type} (u : list A) : npow u 0 = [].
Proof. reflexivity. Qed.

Lemma npow_1 {A : Type} (u : list A) : npow u 1 = u.
Proof. unfold npow; simpl; apply app_nil_r. Qed.

Lemma npow_2 {A : Type} (u : list A) : npow u 2 = u ++ u.
Proof. unfold npow; simpl; rewrite app_nil_r; reflexivity. Qed.

Lemma npow_3 {A : Type} (u : list A) : npow u 3 = u ++ u ++ u.
Proof. unfold npow; simpl; rewrite app_nil_r; reflexivity. Qed.

Lemma npow_add {A : Type} (u : list A) (a b : N) :
  npow u (a + b) = npow u a ++ npow u b.
Proof.
  unfold npow. rewrite N2Nat.inj_add. apply lpow_add.
Qed.

Lemma npow_one_add {A : Type} (u : list A) (n : N) :
  npow u (1 + n) = u ++ npow u n.
Proof.
  rewrite npow_add, npow_1. reflexivity.
Qed.

Lemma npow_succ_right {A : Type} (u : list A) (n : N) :
  npow u n ++ u = npow u (n + 1).
Proof.
  rewrite npow_add, npow_1. reflexivity.
Qed.

Lemma npow_two_add {A : Type} (u : list A) (n : N) :
  npow u (2 + n) = u ++ u ++ npow u n.
Proof.
  rewrite npow_add, npow_2, <- app_assoc. reflexivity.
Qed.

Lemma npow_add_two {A : Type} (u : list A) (n : N) :
  npow u (n + 2) = u ++ u ++ npow u n.
Proof.
  replace (n + 2) with (2 + n) by lia.
  apply npow_two_add.
Qed.

Lemma npow_add_four {A : Type} (u : list A) (n : N) :
  npow u (n + 4) = u ++ u ++ u ++ u ++ npow u n.
Proof.
  replace (n + 4) with (2 + (2 + n)) by lia.
  rewrite !npow_two_add. reflexivity.
Qed.

Lemma npow_mul_two {A : Type} (u : list A) (k : N) :
  npow u (k * 2) = npow (u ++ u) k.
Proof.
  unfold npow.
  replace (N.to_nat (k * 2)) with (N.to_nat k * 2)%nat by lia.
  rewrite lpow_mul. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma npow_append_npow (u : list Sym) (a b : N) (s : side) :
  npow u a *> (npow u b *> s) = npow u (a + b) *> s.
Proof.
  rewrite npow_add, Str_app_assoc. reflexivity.
Qed.

Lemma pow_11_eq_pow_1 (m : N) :
  npow [S1; S1] m = npow [S1] (m * 2).
Proof.
  rewrite npow_mul_two. reflexivity.
Qed.

Lemma pow_111_eq_pow_1 (m : N) :
  npow [S1; S1; S1] m = npow [S1] (m * 3).
Proof.
  unfold npow.
  replace (N.to_nat (m * 3)) with (N.to_nat m * 3)%nat by lia.
  rewrite lpow_mul. reflexivity.
Qed.

Definition D_word (n : N) : list Sym := [S1] ++ npow [S1; S1] n ++ [S0; S0].
Definition S_word (n : N) : list Sym := [S1] ++ npow [S0; S1] (1 + n).
Definition B_word (a c : N) : list Sym :=
  npow [S1; S0] a ++ npow [S1] c ++ S_word 0 ++ S_word 0.

Definition CfgR (l r : side) : Q * tape := l {{B}}> ([S0; S1; S0; S0] *> r).
Definition CfgL (l r : side) : Q * tape := l <{{C}} ([S1] *> r).
Definition CfgJ (l r : side) : Q * tape := l <{{D}} ([S1; S0; S0] *> r).

Lemma rot_pow_cons (a : Sym) (w : list Sym) (k : N) (s : side) :
  npow (a :: w) k *> (a >> s) = a >> (npow (w ++ [a]) k *> s).
Proof.
  unfold npow. apply lpow_rotate.
Qed.

Lemma rot_1 (k : N) (s : side) :
  npow [S1] k *> (S1 >> s) = S1 >> (npow [S1] k *> s).
Proof. exact (rot_pow_cons S1 [] k s). Qed.

Lemma rot_0 (k : N) (s : side) :
  npow [S0] k *> (S0 >> s) = S0 >> (npow [S0] k *> s).
Proof. exact (rot_pow_cons S0 [] k s). Qed.

Lemma rot_01 (k : N) (s : side) :
  npow [S0; S1] k *> (S0 >> s) = S0 >> (npow [S1; S0] k *> s).
Proof. exact (rot_pow_cons S0 [S1] k s). Qed.

Lemma rot_10 (k : N) (s : side) :
  npow [S1; S0] k *> (S1 >> s) = S1 >> (npow [S0; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S0] k s). Qed.

Lemma rot_11 (k : N) (s : side) :
  npow [S1; S1] k *> (S1 >> s) = S1 >> (npow [S1; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S1] k s). Qed.

Lemma rot_0101 (k : N) (s : side) :
  npow [S0; S1; S0; S1] k *> (S0 >> s) = S0 >> (npow [S1; S0; S1; S0] k *> s).
Proof. exact (rot_pow_cons S0 [S1; S0; S1] k s). Qed.

Lemma rot_1010 (k : N) (s : side) :
  npow [S1; S0; S1; S0] k *> (S1 >> s) = S1 >> (npow [S0; S1; S0; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S0; S1; S0] k s). Qed.

Lemma rot_1101 (k : N) (s : side) :
  npow [S1; S1; S0; S1] k *> (S1 >> s) = S1 >> (npow [S1; S0; S1; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S1; S0; S1] k s). Qed.

Lemma rot_1011 (k : N) (s : side) :
  npow [S1; S0; S1; S1] k *> (S1 >> s) = S1 >> (npow [S0; S1; S1; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S0; S1; S1] k s). Qed.

Lemma rot_0111 (k : N) (s : side) :
  npow [S0; S1; S1; S1] k *> (S0 >> s) = S0 >> (npow [S1; S1; S1; S0] k *> s).
Proof. exact (rot_pow_cons S0 [S1; S1; S1] k s). Qed.

Lemma rot_1110 (k : N) (s : side) :
  npow [S1; S1; S1; S0] k *> (S1 >> s) = S1 >> (npow [S1; S1; S0; S1] k *> s).
Proof. exact (rot_pow_cons S1 [S1; S1; S0] k s). Qed.

Lemma hd_const {A : Type} (x : A) : hd (const x) = x.
Proof. reflexivity. Qed.

Lemma zero_cons_default : S0 >> const S0 = const S0.
Proof. symmetry; apply const_unfold. Qed.

Lemma zeros_append_default (k : N) : npow [S0] k *> const S0 = const S0.
Proof.
  unfold npow. apply lpow_all0. exact zero_cons_default.
Qed.

Create HintDb cb discriminated.
#[local] Hint Rewrite
  N.add_0_l N.add_0_r
  @npow_0 @npow_1 @npow_2 @npow_3
  @npow_one_add @npow_two_add @npow_add_two @npow_add_four @npow_mul_two
  @Str_app_assoc npow_append_npow
  @hd_const @tl_const @move_left_const @move_right_const
  zero_cons_default zeros_append_default
  rot_1 rot_0 rot_01 rot_10 rot_11
  rot_0101 rot_1010 rot_1101 rot_1011 rot_0111 rot_1110 : cb.

Ltac norm_cb :=
  unfold CfgR, CfgL, CfgJ, D_word, S_word;
  repeat progress (
    autorewrite with cb;
    cbn [List.app Str_app Streams.hd Streams.tl move_left move_right]
  ).

Ltac step_cb :=
  eapply evstep_step;
  [ prove_step || (norm_cb; prove_step)
  | cbn [List.app Str_app Streams.hd Streams.tl move_left move_right] ].

Tactic Notation "nsteps" int_or_var(k) :=
  norm_cb; do k step_cb.

Ltac eq_lia :=
  reflexivity ||
  lazymatch goal with
  | |- @eq N _ _ => lia
  | |- @eq nat _ _ => lia
  | |- _ = _ => progress f_equal; eq_lia
  end.

Ltac finish_cb :=
  norm_cb; apply evstep_refl'; eq_lia.

Ltac check_done_cb :=
  lazymatch goal with
  | |- (?q, _) -->* (?q, _) => finish_cb
  end.

Ltac fsteps :=
  norm_cb;
  do 60 (try solve [check_done_cb]; try step_cb);
  finish_cb.

Tactic Notation "follow_cb" uconstr(H) :=
  norm_cb; eapply evstep_trans; [eapply H | norm_cb].

Lemma N_ind_1_add (P : N -> Prop)
  (H0 : P 0) (HS : forall n : N, P n -> P (1 + n)) :
  forall n : N, P n.
Proof.
  intro n. induction n using N.peano_ind.
  - exact H0.
  - replace (N.succ n) with (1 + n) by lia. exact (HS n IHn).
Qed.

Lemma scanR_plain (l r : side) (n : N) :
  (B;; l {{S0}} (npow [S1; S1] n *> r)) -->*
  (B;; (npow [S1; S0] n *> l) {{S0}} r).
Proof.
  revert l. induction n as [| n ih] using N_ind_1_add; intro l.
  - finish_cb.
  - nsteps 6.
    eapply evstep_trans; [apply (ih (S1 >> S0 >> l)) |].
    finish_cb.
Qed.

Lemma scanR (l r : side) (n : N) :
  (B;; l {{S0}} (S1 >> (npow [S1; S1] n *> r))) -->*
  (B;; (npow [S1; S0] n *> l) {{S0}} (S1 >> r)).
Proof.
  rewrite <- rot_11.
  exact (scanR_plain l (S1 >> r) n).
Qed.

Lemma scanR1 (l r : side) (n : N) :
  (B;; l {{S0}} (S1 >> S1 >> (npow [S1; S1] n *> r))) -->*
  (B;; (npow [S1; S0] n *> l) {{S0}} (S1 >> S1 >> r)).
Proof.
  rewrite <- (rot_11 n r).
  exact (scanR l (S1 >> r) n).
Qed.

Lemma scanB (l r : side) (n : N) :
  ((npow [S0; S1] n *> l) <{{C}} r) -->*
  (l <{{C}} (npow [S1; S1] n *> r)).
Proof.
  revert r. induction n as [| n ih] using N_ind_1_add; intro r.
  - finish_cb.
  - nsteps 2.
    eapply evstep_trans; [apply (ih ([S1; S1] *> r)) |].
    finish_cb.
Qed.

Lemma scanC (l r : side) (n : N) :
  ((npow [S1; S0] n *> l) <{{D}} r) -->*
  (l <{{D}} (npow [S1; S1] n *> r)).
Proof.
  revert r. induction n as [| n ih] using N_ind_1_add; intro r.
  - finish_cb.
  - nsteps 2.
    eapply evstep_trans; [apply (ih ([S1; S1] *> r)) |].
    finish_cb.
Qed.

Lemma scanPair (l r : side) (n : N) :
  (B;; l {{S0}} (S1 >> (npow [S0; S1; S0; S1] n *> r))) -->*
  (B;; (npow [S1; S1; S0; S1] n *> l) {{S0}} (S1 >> r)).
Proof.
  revert l. induction n as [| n ih] using N_ind_1_add; intro l.
  - finish_cb.
  - nsteps 4.
    eapply evstep_trans; [apply (ih (S1 >> S1 >> S0 >> S1 >> l)) |].
    finish_cb.
Qed.

Lemma ones (l r : side) (n : N) :
  (l {{B}}> (npow [S1] n *> r)) -->*
  ((npow [S1] n *> l) {{B}}> r).
Proof.
  revert l. induction n as [| n ih] using N_ind_1_add; intro l.
  - finish_cb.
  - nsteps 1.
    eapply evstep_trans; [apply (ih ([S1] *> l)) |].
    finish_cb.
Qed.

Lemma ones2 (l r : side) (n : N) :
  (l {{B}}> (npow [S1; S1] n *> r)) -->*
  ((npow [S1; S1] n *> l) {{B}}> r).
Proof.
  rewrite pow_11_eq_pow_1.
  exact (ones l r (n * 2)).
Qed.

Lemma rule_init :
  c0 -->* CfgL ([S1] *> 0inf) ([S1] *> 0inf).
Proof.
  unfold c0, tape0, q0, s0.
  fsteps.
Qed.

Lemma rule_halt (l r : side) :
  halts tm (CfgL ([S0; S0; S1; S1; S1] *> l) r).
Proof.
  unfold CfgL.
  do 4 (eapply halts_step; [| prove_step]; simpl_tape).
  apply halted_halts.
  reflexivity.
Qed.

Lemma rule_right (l r : side) (n : N) :
  CfgR l (D_word n *> r) -->* CfgR (S_word n *> l) r.
Proof.
  nsteps 3. follow_cb (scanR _ _ n). finish_cb.
Qed.

Lemma rule_right_pow (l r : side) (n k : N) :
  CfgR l (npow (D_word n) k *> r) -->* CfgR (npow (S_word n) k *> l) r.
Proof.
  revert l. induction k as [| k ih] using N_ind_1_add; intro l.
  - finish_cb.
  - rewrite npow_one_add, Str_app_assoc.
    eapply evstep_trans; [apply (rule_right l (npow (D_word n) k *> r) n) |].
    eapply evstep_trans; [apply (ih (S_word n *> l)) |].
    replace (1 + k) with (k + 1) by lia.
    rewrite <- npow_succ_right, Str_app_assoc.
    apply evstep_refl.
Qed.

Lemma rule_left (l r : side) (n : N) :
  CfgL (S_word n *> l) r -->* CfgL l (D_word n *> r).
Proof.
  nsteps 5. follow_cb (scanB _ _ n). finish_cb.
Qed.

Lemma rule_left_pow (l r : side) (n k : N) :
  CfgL (npow (S_word n) k *> l) r -->* CfgL l (npow (D_word n) k *> r).
Proof.
  revert r. induction k as [| k ih] using N_ind_1_add; intro r.
  - finish_cb.
  - rewrite npow_one_add, Str_app_assoc.
    eapply evstep_trans; [apply (rule_left (npow (S_word n) k *> l) r n) |].
    eapply evstep_trans; [apply (ih (D_word n *> r)) |].
    replace (1 + k) with (k + 1) by lia.
    rewrite <- npow_succ_right, Str_app_assoc.
    apply evstep_refl.
Qed.

Lemma rule_even (l r : side) (n : N) :
  CfgR l (npow [S1; S1] (1 + n) *> ([S0; S0] *> r)) -->*
  CfgL l (D_word (1 + n) *> ([S1; S0] *> r)).
Proof.
  nsteps 3. follow_cb (scanR1 _ _ n). nsteps 16. follow_cb (scanB _ _ n). finish_cb.
Qed.

Lemma rule_restart (l r : side) (b : N) :
  CfgL (npow [S1; S0] (1 + b) *> ([S1; S1; S1] *> l)) r -->*
  CfgR (npow [S1; S0] (1 + b) *> l) r.
Proof.
  assert (H : npow [S1; S0] (1 + b) *> ([S1; S1; S1] *> l) =
              S_word b *> ([S1; S1] *> l)) by (norm_cb; reflexivity).
  rewrite H.
  eapply evstep_trans; [apply (rule_left ([S1; S1] *> l) r b) |].
  nsteps 5. follow_cb (scanR _ _ b). finish_cb.
Qed.

Lemma rule_overflow2 (r : side) (b : N) :
  CfgL (npow [S1; S0] (1 + b) *> ([S1; S1] *> 0inf)) r -->*
  CfgR (npow [S1; S0] 2 *> (npow [S1; S1] (1 + b) *> 0inf)) ([S1] *> r).
Proof.
  nsteps 5. follow_cb (scanB _ _ b). nsteps 16. follow_cb (scanR1 _ _ b).
  nsteps 16. follow_cb (scanB _ _ b). nsteps 9. follow_cb (ones2 _ _ b). fsteps.
Qed.

Lemma rule_overflow1 (r : side) (b n : N) :
  CfgL (npow [S1; S0] (1 + b) *> ([S1] *> 0inf)) (D_word n *> r) -->*
  CfgR (npow [S1; S0] (n + 2) *> (npow [S1; S1] b *> 0inf)) ([S1; S0] *> r).
Proof.
  nsteps 5. follow_cb (scanB _ _ b). nsteps 7. follow_cb (ones2 _ _ b).
  nsteps 8. follow_cb (scanR1 _ _ n). nsteps 16. follow_cb (scanB _ _ n).
  nsteps 11. follow_cb (scanR _ _ n). finish_cb.
Qed.

Lemma rule_leftJ (l r : side) (n : N) :
  CfgJ (S_word n *> l) r -->* CfgL l (D_word (1 + n) *> r).
Proof.
  nsteps 3. follow_cb (scanB _ _ n). finish_cb.
Qed.

Lemma rule_turnB (l r : side) (n : N) :
  CfgL ([S1; S1] *> l) (D_word n *> r) -->*
  CfgR (npow [S1; S0] (1 + n) *> l) r.
Proof.
  nsteps 5. follow_cb (scanR _ _ n). finish_cb.
Qed.

Lemma rule_turnJ (l r : side) (b : N) :
  CfgJ (npow [S1; S0] b *> ([S1; S1; S1] *> l)) r -->*
  CfgR (npow [S1; S0] (1 + b) *> l) r.
Proof.
  nsteps 1. follow_cb (scanB _ _ b). nsteps 5. follow_cb (scanR _ _ b). finish_cb.
Qed.

Lemma rule_finishP (l r : side) (b : N) :
  CfgL (npow [S1; S0] (1 + b) *> ([S0; S1] *> (S_word 0 *> l))) r -->*
  CfgJ l (D_word (1 + b) *> r).
Proof.
  nsteps 4. follow_cb (scanC _ _ b). fsteps.
Qed.

Lemma rule_defect0 (l r : side) (m : N) :
  CfgR l ([S1; S0] *> (D_word 0 *> ([S1] *> (npow [S1; S1] m *> ([S0] *> r))))) -->*
  CfgJ l ([S1; S1; S1; S1] *> (D_word m *> ([S1] *> r))).
Proof.
  nsteps 15. follow_cb (scanR1 _ _ m). nsteps 15. follow_cb (scanC _ _ m). fsteps.
Qed.

Lemma rule_defect0_D (l r : side) (m : N) :
  CfgR l ([S1; S0] *> (D_word 0 *> (D_word m *> r))) -->*
  CfgJ l (D_word (m + 2) *> ([S1; S0] *> r)).
Proof.
  pose proof (rule_defect0 l (S0 >> r) m) as h.
  assert (hl : [S1] *> (npow [S1; S1] m *> ([S0] *> (S0 >> r))) = D_word m *> r)
    by (norm_cb; reflexivity).
  assert (hr : [S1; S1; S1; S1] *> (D_word m *> ([S1] *> (S0 >> r))) =
               D_word (m + 2) *> ([S1; S0] *> r))
    by (norm_cb; reflexivity).
  rewrite hl, hr in h.
  exact h.
Qed.

Lemma rule_defect1 (l r : side) (m : N) :
  CfgR l ([S1; S0] *> (D_word 1 *> ([S1] *> (npow [S1; S1] m *> ([S0] *> r))))) -->*
  CfgL l (D_word 0 *> (D_word 0 *> (D_word (1 + m) *> ([S1] *> r)))).
Proof.
  nsteps 17. follow_cb (scanR1 _ _ m). nsteps 16. follow_cb (scanB _ _ m). fsteps.
Qed.

Lemma rule_defect1_D (l r : side) (m : N) :
  CfgR l ([S1; S0] *> (D_word 1 *> (D_word m *> r))) -->*
  CfgL l (D_word 0 *> (D_word 0 *> (D_word (1 + m) *> ([S1; S0] *> r)))).
Proof.
  pose proof (rule_defect1 l (S0 >> r) m) as h.
  assert (hl : [S1] *> (npow [S1; S1] m *> ([S0] *> (S0 >> r))) = D_word m *> r)
    by (norm_cb; reflexivity).
  assert (hr : [S1] *> (S0 >> r) = [S1; S0] *> r)
    by reflexivity.
  rewrite hl, hr in h.
  exact h.
Qed.

Lemma rule_defect2 (l r : side) (n m : N) :
  CfgR l ([S1; S0] *> (D_word (2 + n) *> ([S1] *> (npow [S1; S1] m *> ([S0] *> r))))) -->*
  CfgR (B_word (2 + m) (2 * n) *> l) ([S1] *> r).
Proof.
  assert (hB : B_word (2 + m) (2 * n) *> l =
               npow [S1; S0] (2 + m) *> (npow [S1; S1] n *> (S_word 0 *> (S_word 0 *> l)))).
  { unfold B_word. replace (2 * n) with (n * 2) by lia.
    rewrite <- pow_11_eq_pow_1, !Str_app_assoc. reflexivity. }
  rewrite hB.
  nsteps 11. follow_cb (ones2 _ _ n). nsteps 8. follow_cb (scanR1 _ _ m).
  nsteps 16. follow_cb (scanB _ _ m). nsteps 11. follow_cb (scanR _ _ m). finish_cb.
Qed.

Lemma rule_defect2_D (l r : side) (n m : N) :
  CfgR l ([S1; S0] *> (D_word (2 + n) *> (D_word m *> r))) -->*
  CfgR (B_word (2 + m) (2 * n) *> l) ([S1; S0] *> r).
Proof.
  pose proof (rule_defect2 l (S0 >> r) n m) as h.
  assert (hl : [S1] *> (npow [S1; S1] m *> ([S0] *> (S0 >> r))) = D_word m *> r)
    by (norm_cb; reflexivity).
  assert (hr : [S1] *> (S0 >> r) = [S1; S0] *> r)
    by reflexivity.
  rewrite hl, hr in h.
  exact h.
Qed.

Lemma rule_defect2_D_pair_pow (l r : side) (n k : N) :
  CfgR l ([S1; S0] *> (npow (D_word (2 + n)) (2 * k) *> r)) -->*
  CfgR (npow (B_word (4 + n) (2 * n)) k *> l) ([S1; S0] *> r).
Proof.
  revert l. induction k as [| k ih] using N_ind_1_add; intro l.
  - replace (2 * 0) with 0 by lia. finish_cb.
  - replace (2 * (1 + k)) with (2 + 2 * k) by lia.
    rewrite npow_two_add, !Str_app_assoc.
    eapply evstep_trans; [apply (rule_defect2_D l (npow (D_word (2 + n)) (2 * k) *> r) n (2 + n)) |].
    replace (2 + (2 + n)) with (4 + n) by lia.
    eapply evstep_trans; [apply (ih (B_word (4 + n) (2 * n) *> l)) |].
    replace (1 + k) with (k + 1) by lia.
    rewrite <- npow_succ_right, Str_app_assoc.
    apply evstep_refl.
Qed.

Lemma rule_defect_blank0 (l r : side) :
  CfgR l ([S1; S0] *> (D_word 0 *> ([S0; S0] *> r))) -->*
  CfgR ([S1; S0] *> ([S0; S1] *> (S_word 0 *> l))) r.
Proof.
  fsteps.
Qed.

Lemma rule_paired (l r : side) (k n : N) :
  CfgR l (npow [S1; S0] (k * 2) *> (D_word n *> r)) -->*
  CfgR (npow [S1; S0] n *> (npow [S1; S1; S0; S1] k *> (S_word 0 *> l))) r.
Proof.
  nsteps 3. follow_cb (scanPair _ _ k). follow_cb (scanR _ _ n). finish_cb.
Qed.

Lemma rule_emptyR (l : side) :
  CfgR l 0inf -->* CfgL l (D_word 0 *> (D_word 0 *> 0inf)).
Proof.
  fsteps.
Qed.

Lemma rule_ML_01 (l r : side) (k : N) :
  CfgL (npow [S0; S1] k *> l) r -->*
  CfgL l (npow [S1; S1] k *> r).
Proof.
  unfold CfgL. simpl.
  rewrite <- rot_11.
  exact (scanB l (S1 >> r) k).
Qed.

Lemma rule_ML_10 (l r : side) :
  CfgL ([S1; S0] *> l) r -->* CfgJ l r.
Proof.
  fsteps.
Qed.

Lemma rule_MJ_default (r : side) :
  CfgJ 0inf r -->* CfgL ([S1; S1; S1] *> 0inf) ([S1] *> r).
Proof.
  fsteps.
Qed.

Lemma rule_ML_default (r : side) (k : N) :
  CfgL 0inf (npow [S1] k *> ([S0; S0] *> r)) -->*
  CfgL (npow [S1] (k + 4) *> 0inf) ([S1] *> r).
Proof.
  assert (hk4 : npow [S1] (k + 4) *> 0inf = npow [S1] k *> ([S1; S1; S1; S1] *> 0inf)).
  { replace (k + 4) with (k + (2 + 2)) by lia.
    rewrite npow_add, npow_two_add, npow_2, !Str_app_assoc. reflexivity. }
  rewrite hk4.
  nsteps 6. follow_cb (ones _ _ k). fsteps.
Qed.

Lemma rule_ML_TurnB_even (l r : side) (k : N) :
  CfgL ([S1; S1] *> l) (npow [S1; S1] k *> ([S0] *> r)) -->*
  CfgL (npow [S1; S0] (k + 1) *> l) ([S1] *> r).
Proof.
  rewrite <- npow_succ_right, Str_app_assoc.
  nsteps 5. follow_cb (scanR_plain _ _ k). fsteps.
Qed.

Lemma rule_MR_PairedEven (l r : side) (m : N) :
  CfgR l ([S1; S0; S1; S0] *> (npow [S1; S1] m *> ([S0; S0] *> r))) -->*
  CfgL (npow [S1; S0] m *> ([S1; S1; S0; S1] *> (S_word 0 *> l))) ([S1; S0] *> r).
Proof.
  nsteps 7. follow_cb (scanR_plain _ _ m). fsteps.
Qed.

Lemma rule_MR_110 (l r : side) :
  CfgR l ([S1; S1; S0] *> r) -->*
  CfgL (S_word 1 *> l) ([S1] *> r).
Proof.
  fsteps.
Qed.

Lemma rule_MR_PairedOdd (l r : side) (n : N) :
  CfgR l (npow [S1; S0] 3 *> (D_word n *> r)) -->*
  CfgL (npow [S1; S1] n *> (npow [S1; S1; S0; S1] 2 *> (S_word 0 *> l))) ([S1] *> r).
Proof.
  nsteps 11. follow_cb (ones2 _ _ n). fsteps.
Qed.

(* ========================================================================== *)
(* Section 2: OneCall, NCalls, and B_word Macro Lemmas                        *)
(* ========================================================================== *)

Definition OneCall (r r' : side) : Prop :=
  forall l, CfgR l r -->* CfgL l r'.

Lemma OneCall_prepend_D (n : N) {r r' : side} (h : OneCall r r') :
  OneCall (D_word n *> r) (D_word n *> r').
Proof.
  intro l.
  eapply evstep_trans; [apply (rule_right l r n) |].
  eapply evstep_trans; [apply (h (S_word n *> l)) |].
  exact (rule_left l r' n).
Qed.

Lemma OneCall_prepend_D_pow (n k : N) {r r' : side} (h : OneCall r r') :
  OneCall (npow (D_word n) k *> r) (npow (D_word n) k *> r').
Proof.
  induction k as [| k ih] using N_ind_1_add.
  - rewrite npow_0. exact h.
  - rewrite !npow_one_add, !Str_app_assoc.
    exact (OneCall_prepend_D n ih).
Qed.

Lemma OneCall_default :
  OneCall 0inf (D_word 0 *> (D_word 0 *> 0inf)).
Proof.
  exact rule_emptyR.
Qed.

Lemma OneCall_D0_pow (d0 : N) :
  OneCall (npow (D_word 0) d0 *> 0inf) (npow (D_word 0) (d0 + 2) *> 0inf).
Proof.
  pose proof (OneCall_prepend_D_pow 0 d0 OneCall_default) as h.
  replace (npow (D_word 0) (d0 + 2) *> 0inf)
    with (npow (D_word 0) d0 *> (D_word 0 *> (D_word 0 *> 0inf))).
  - exact h.
  - replace (d0 + 2) with ((d0 + 1) + 1) by lia.
    rewrite <- !npow_succ_right, !Str_app_assoc. reflexivity.
Qed.

Lemma OneCall_defect0 (j d : N) (r : side) :
  OneCall (D_word j *> ([S1; S0] *> (D_word 0 *> (D_word d *> r))))
          (D_word (j + 1) *> (D_word (d + 2) *> ([S1; S0] *> r))).
Proof.
  intro l.
  eapply evstep_trans; [eapply (rule_right l _ j) |].
  eapply evstep_trans; [apply (rule_defect0_D (S_word j *> l) r d) |].
  replace (j + 1) with (1 + j) by lia.
  exact (rule_leftJ l (D_word (d + 2) *> ([S1; S0] *> r)) j).
Qed.

Lemma OneCall_defect1 (d : N) (r : side) :
  OneCall ([S1; S0] *> (D_word 1 *> (D_word d *> r)))
          (D_word 0 *> (D_word 0 *> (D_word (d + 1) *> ([S1; S0] *> r)))).
Proof.
  intro l.
  replace (d + 1) with (1 + d) by lia.
  exact (rule_defect1_D l r d).
Qed.

Inductive NCallsNat : nat -> side -> side -> Prop :=
  | NCallsNat_zero (r : side) : NCallsNat 0%nat r r
  | NCallsNat_succ {n : nat} {r1 r2 r3 : side} :
      OneCall r1 r2 -> NCallsNat n r2 r3 -> NCallsNat (S n) r1 r3.

Definition NCalls (n : N) (r r' : side) : Prop :=
  NCallsNat (N.to_nat n) r r'.

Lemma NCalls_zero (r : side) : NCalls 0 r r.
Proof. constructor. Qed.

Lemma NCalls_succ {n : N} {r1 r2 r3 : side} (h1 : OneCall r1 r2) (h2 : NCalls n r2 r3) :
  NCalls (n + 1) r1 r3.
Proof.
  unfold NCalls in *.
  replace (N.to_nat (n + 1)) with (S (N.to_nat n)) by lia.
  exact (NCallsNat_succ h1 h2).
Qed.

Lemma OneCall_of_NCalls_one {r r' : side} (h : NCalls 1 r r') : OneCall r r'.
Proof.
  unfold NCalls in h. change (N.to_nat 1) with 1%nat in h.
  inversion h as [| ? ? r2 ? h1 h0]; subst.
  inversion h0; subst.
  exact h1.
Qed.

Lemma NCalls_prepend_D (d : N) {n : N} {r r' : side} (h : NCalls n r r') :
  NCalls n (D_word d *> r) (D_word d *> r').
Proof.
  unfold NCalls in *.
  induction h as [r0 | k r1 r2 r3 h1 _ ih].
  - constructor.
  - exact (NCallsNat_succ (OneCall_prepend_D d h1) ih).
Qed.

Lemma NCalls_prepend_D_pow (d k : N) {n : N} {r r' : side} (h : NCalls n r r') :
  NCalls n (npow (D_word d) k *> r) (npow (D_word d) k *> r').
Proof.
  induction k as [| k ih] using N_ind_1_add.
  - rewrite npow_0. exact h.
  - rewrite !npow_one_add, !Str_app_assoc.
    exact (NCalls_prepend_D d ih).
Qed.

Lemma NCalls_from_ML (n b : N) (l r r' : side) (h : NCalls n r r') :
  CfgL (npow [S1; S0] (1 + b) *> (npow [S1; S1; S1] n *> l)) r -->*
  CfgL (npow [S1; S0] (1 + b) *> l) r'.
Proof.
  unfold NCalls, npow in *.
  remember (N.to_nat n) as k eqn:Hk; clear n Hk.
  induction h as [r0 | k r1 r2 r3 h1 _ ih].
  - simpl. apply evstep_refl.
  - change (([S1; S1; S1] ^^ S k) *> l) with ([S1; S1; S1] *> (([S1; S1; S1] ^^ k) *> l)).
    eapply evstep_trans; [apply (rule_restart (([S1; S1; S1] ^^ k) *> l) r1 b) |].
    eapply evstep_trans; [apply (h1 (([S1; S0] ^^ N.to_nat (1 + b)) *> (([S1; S1; S1] ^^ k) *> l))) |].
    exact ih.
Qed.

Lemma NCalls_from_MR (m b : N) (l r r' : side) (h : NCalls (m + 1) r r') :
  CfgR (npow [S1; S0] (1 + b) *> (npow [S1; S1; S1] m *> l)) r -->*
  CfgL (npow [S1; S0] (1 + b) *> l) r'.
Proof.
  unfold NCalls in h.
  replace (N.to_nat (m + 1)) with (S (N.to_nat m)) in h by lia.
  inversion h as [| ? ? rmid ? h1 hrest]; subst.
  eapply evstep_trans; [apply (h1 _) |].
  exact (NCalls_from_ML m b l rmid r' hrest).
Qed.

Lemma NCalls_collide_pow (m j : N) (r : side) :
  NCalls (m + 1)
    (D_word j *> ([S1; S0] *> (npow (D_word 0) (2 * (m + 1)) *> r)))
    (D_word (j + 1) *> (npow (D_word 3) m *> (D_word 2 *> ([S1; S0] *> r)))).
Proof.
  revert j. induction m as [| m ih] using N_ind_1_add; intro j.
  - replace (2 * (0 + 1)) with 2 by lia.
    rewrite npow_2, npow_0, Str_app_assoc. simpl Str_app.
    exact (NCalls_succ (OneCall_defect0 j 0 r) (NCalls_zero _)).
  - replace (2 * (1 + m + 1)) with (2 + 2 * (m + 1)) by lia.
    rewrite npow_two_add, !Str_app_assoc.
    replace (1 + m + 1) with ((m + 1) + 1) by lia.
    eapply NCalls_succ.
    + exact (OneCall_defect0 j 0 (npow (D_word 0) (2 * (m + 1)) *> r)).
    + rewrite (npow_one_add (D_word 3) m), Str_app_assoc.
      exact (NCalls_prepend_D (j + 1) (ih 2)).
Qed.

Lemma NCalls_D0_pow (n d0 : N) :
  NCalls n (npow (D_word 0) d0 *> 0inf) (npow (D_word 0) (d0 + 2 * n) *> 0inf).
Proof.
  revert d0. induction n as [| n ih] using N_ind_1_add; intro d0.
  - replace (d0 + 2 * 0) with d0 by lia. apply NCalls_zero.
  - replace (1 + n) with (n + 1) by lia.
    eapply NCalls_succ.
    + exact (OneCall_D0_pow d0).
    + replace (d0 + 2 * (n + 1)) with ((d0 + 2) + 2 * n) by lia.
      exact (ih (d0 + 2)).
Qed.

Lemma w10_pow_one_eq_S (n : N) (x : side) :
  npow [S1; S0] (1 + n) *> (S1 >> x) = S_word n *> x.
Proof.
  norm_cb; reflexivity.
Qed.

Lemma w10_pow_S0_eq_S (a : N) (x : side) :
  npow [S1; S0] a *> (S_word 0 *> x) = S_word a *> x.
Proof.
  norm_cb; reflexivity.
Qed.

Lemma B_word_r2_eq (a q : N) (l : side) :
  B_word a (3 * q + 2) *> l =
    npow [S1; S0] a *> (npow [S1; S1; S1] (q + 1) *> ([S0; S1] *> (S_word 0 *> l))).
Proof.
  unfold B_word.
  assert (h1 : npow [S1] (3 * q + 2) = npow [S1; S1; S1] q ++ [S1; S1]).
  { rewrite npow_add, pow_111_eq_pow_1, npow_2. replace (q * 3) with (3 * q) by lia. reflexivity. }
  assert (h2 : npow [S1; S1; S1] (q + 1) = npow [S1; S1; S1] q ++ [S1; S1; S1]).
  { rewrite <- npow_succ_right. reflexivity. }
  rewrite h1, h2. unfold S_word.
  rewrite !npow_one_add, !npow_0, !Str_app_assoc. simpl. reflexivity.
Qed.

Lemma B_word_r0_eq (a q : N) (l : side) :
  B_word a (3 * q) *> l =
    npow [S1; S0] a *> (npow [S1; S1; S1] q *> (S_word 0 *> (S_word 0 *> l))).
Proof.
  unfold B_word.
  replace (3 * q) with (q * 3) by lia.
  rewrite <- pow_111_eq_pow_1, !Str_app_assoc. reflexivity.
Qed.

Lemma B_word_r1_eq (a q : N) (l : side) :
  B_word a (3 * q + 1) *> l =
    npow [S1; S0] a *> (npow [S1; S1; S1] q *> (S1 >> (S_word 0 *> (S_word 0 *> l)))).
Proof.
  unfold B_word.
  rewrite npow_add, npow_1.
  replace (3 * q) with (q * 3) by lia.
  rewrite <- pow_111_eq_pow_1, !Str_app_assoc. simpl. reflexivity.
Qed.

Lemma B_word_ML_r2 (a q : N) (l r r' : side) (hc : NCalls (q + 1) r r') :
  CfgL (B_word (1 + a) (3 * q + 2) *> l) r -->*
  CfgJ l (D_word (1 + a) *> r').
Proof.
  rewrite B_word_r2_eq.
  eapply evstep_trans; [apply (NCalls_from_ML (q + 1) a ([S0; S1] *> (S_word 0 *> l)) r r' hc) |].
  exact (rule_finishP l r' a).
Qed.

Lemma B_word_MJ_r2 (a q : N) (l r r' : side) (hc : NCalls (q + 1) r r') :
  CfgJ (B_word (1 + a) (3 * q + 2) *> l) r -->*
  CfgJ l (D_word (2 + a) *> r').
Proof.
  rewrite B_word_r2_eq.
  replace (q + 1) with (1 + q) by lia.
  rewrite (npow_one_add [S1; S1; S1] q), Str_app_assoc.
  eapply evstep_trans; [apply (rule_turnJ (npow [S1; S1; S1] q *> ([S0; S1] *> (S_word 0 *> l))) r (1 + a)) |].
  replace (1 + (1 + a)) with (1 + (a + 1)) by lia.
  replace (1 + q) with (q + 1) in hc by lia.
  eapply evstep_trans; [apply (NCalls_from_MR q (a + 1) ([S0; S1] *> (S_word 0 *> l)) r r' hc) |].
  replace (2 + a) with (1 + (a + 1)) by lia.
  exact (rule_finishP l r' (a + 1)).
Qed.

Lemma NCallsNat_decomp (n m : nat) (x z : side) (hnm : NCallsNat (n + m)%nat x z) :
  exists y, NCallsNat n x y /\ NCallsNat m y z.
Proof.
  revert x hnm. induction n as [| n ihn]; intros x hnm.
  - exists x. split; [constructor | exact hnm].
  - simpl in hnm. inversion hnm as [| ? ? x2 ? h1 hrest]; subst.
    destruct (ihn x2 hrest) as [y [hy1 hy2]].
    exists y. split; [exact (NCallsNat_succ h1 hy1) | exact hy2].
Qed.

Lemma NCalls_decomp (n m : N) (x z : side) (hnm : NCalls (n + m) x z) :
  exists y, NCalls n x y /\ NCalls m y z.
Proof.
  unfold NCalls in *. rewrite N2Nat.inj_add in hnm.
  exact (NCallsNat_decomp (N.to_nat n) (N.to_nat m) x z hnm).
Qed.

Lemma B_word_MJ_r2_pow (a q k : N) (l r r' : side)
  (hc : NCalls (k * (q + 1)) r r') :
  CfgJ (npow (B_word (1 + a) (3 * q + 2)) k *> l) r -->*
  CfgJ l (npow (D_word (2 + a)) k *> r').
Proof.
  revert r r' hc. induction k as [| k ih] using N_ind_1_add; intros r r' hc.
  - replace (0 * (q + 1)) with 0 in hc by lia.
    unfold NCalls in hc. inversion hc; subst.
    rewrite !npow_0. simpl. apply evstep_refl.
  - replace ((1 + k) * (q + 1)) with ((q + 1) + k * (q + 1)) in hc by lia.
    destruct (NCalls_decomp (q + 1) (k * (q + 1)) r r' hc) as [rmid [h1 h2]].
    rewrite npow_one_add, Str_app_assoc.
    eapply evstep_trans; [apply (B_word_MJ_r2 a q (npow (B_word (1 + a) (3 * q + 2)) k *> l) r rmid h1) |].
    eapply evstep_trans; [apply (ih (D_word (2 + a) *> rmid) (D_word (2 + a) *> r') (NCalls_prepend_D (2 + a) h2)) |].
    replace (1 + k) with (k + 1) by lia.
    rewrite <- npow_succ_right, Str_app_assoc. apply evstep_refl.
Qed.

Lemma B_word_ML_r2_pow (a q k : N) (l r r' : side)
  (hc : NCalls ((1 + k) * (q + 1)) r r') :
  CfgL (npow (B_word (1 + a) (3 * q + 2)) (1 + k) *> l) r -->*
  CfgJ l (npow (D_word (2 + a)) k *> (D_word (1 + a) *> r')).
Proof.
  replace ((1 + k) * (q + 1)) with ((q + 1) + k * (q + 1)) in hc by lia.
  destruct (NCalls_decomp (q + 1) (k * (q + 1)) r r' hc) as [rmid [h1 h2]].
  rewrite npow_one_add, Str_app_assoc.
  eapply evstep_trans; [apply (B_word_ML_r2 a q (npow (B_word (1 + a) (3 * q + 2)) k *> l) r rmid h1) |].
  exact (B_word_MJ_r2_pow a q k l (D_word (1 + a) *> rmid) (D_word (1 + a) *> r') (NCalls_prepend_D (1 + a) h2)).
Qed.

Lemma B_word_ML_r0 (a q : N) (l r r' : side) (hc : NCalls q r r') :
  CfgL (B_word (1 + a) (3 * q) *> l) r -->*
  CfgL l (D_word 0 *> (D_word (1 + a) *> r')).
Proof.
  rewrite B_word_r0_eq.
  eapply evstep_trans; [apply (NCalls_from_ML q a (S_word 0 *> (S_word 0 *> l)) r r' hc) |].
  rewrite w10_pow_S0_eq_S.
  eapply evstep_trans; [apply (rule_left (S_word 0 *> l) r' (1 + a)) |].
  exact (rule_left l (D_word (1 + a) *> r') 0).
Qed.

Lemma B_word_ML_r1 (a q : N) (l r r' : side) (hc : NCalls q r r') :
  CfgL (B_word (1 + a) (3 * q + 1) *> l) r -->*
  CfgL l (D_word 0 *> (D_word 0 *> (D_word a *> r'))).
Proof.
  rewrite B_word_r1_eq.
  eapply evstep_trans; [apply (NCalls_from_ML q a (S1 >> (S_word 0 *> (S_word 0 *> l))) r r' hc) |].
  rewrite w10_pow_one_eq_S.
  eapply evstep_trans; [apply (rule_left (S_word 0 *> (S_word 0 *> l)) r' a) |].
  eapply evstep_trans; [apply (rule_left (S_word 0 *> l) (D_word a *> r') 0) |].
  exact (rule_left l (D_word 0 *> (D_word a *> r')) 0).
Qed.

Lemma B_word_MJ_r0 (a q : N) (l r r' : side) (hc : NCalls (q + 1) r r') :
  CfgJ (B_word (1 + a) (3 * (q + 1)) *> l) r -->*
  CfgL l (D_word 0 *> (D_word (2 + a) *> r')).
Proof.
  rewrite B_word_r0_eq.
  replace (q + 1) with (1 + q) by lia.
  rewrite (npow_one_add [S1; S1; S1] q), Str_app_assoc.
  eapply evstep_trans; [apply (rule_turnJ (npow [S1; S1; S1] q *> (S_word 0 *> (S_word 0 *> l))) r (1 + a)) |].
  replace (1 + (1 + a)) with (1 + (a + 1)) by lia.
  replace (1 + q) with (q + 1) in hc by lia.
  eapply evstep_trans; [apply (NCalls_from_MR q (a + 1) (S_word 0 *> (S_word 0 *> l)) r r' hc) |].
  rewrite w10_pow_S0_eq_S.
  replace (1 + (a + 1)) with (2 + a) by lia.
  eapply evstep_trans; [apply (rule_left (S_word 0 *> l) r' (2 + a)) |].
  exact (rule_left l (D_word (2 + a) *> r') 0).
Qed.

Lemma B_word_MJ_r1 (a q : N) (l r r' : side) (hc : NCalls (q + 1) r r') :
  CfgJ (B_word (1 + a) (3 * (q + 1) + 1) *> l) r -->*
  CfgL l (D_word 0 *> (D_word 0 *> (D_word (1 + a) *> r'))).
Proof.
  rewrite B_word_r1_eq.
  replace (q + 1) with (1 + q) by lia.
  rewrite (npow_one_add [S1; S1; S1] q), Str_app_assoc.
  eapply evstep_trans; [apply (rule_turnJ (npow [S1; S1; S1] q *> (S1 >> (S_word 0 *> (S_word 0 *> l)))) r (1 + a)) |].
  replace (1 + (1 + a)) with (1 + (a + 1)) by lia.
  replace (1 + q) with (q + 1) in hc by lia.
  eapply evstep_trans; [apply (NCalls_from_MR q (a + 1) (S1 >> (S_word 0 *> (S_word 0 *> l))) r r' hc) |].
  rewrite w10_pow_one_eq_S.
  replace (a + 1) with (1 + a) by lia.
  eapply evstep_trans; [apply (rule_left (S_word 0 *> (S_word 0 *> l)) r' (1 + a)) |].
  eapply evstep_trans; [apply (rule_left (S_word 0 *> l) (D_word (1 + a) *> r') 0) |].
  exact (rule_left l (D_word 0 *> (D_word (1 + a) *> r')) 0).
Qed.

Lemma B_word_turnJ (ba bc : N) (hbc : 3 <= bc) (l r : side) :
  CfgJ (B_word ba bc *> l) r -->*
  CfgR (B_word (ba + 1) (bc - 3) *> l) r.
Proof.
  assert (hsplit : npow [S1] bc = [S1; S1; S1] ++ npow [S1] (bc - 3)).
  { replace bc with (3 + (bc - 3)) at 1 by lia.
    rewrite npow_add, npow_3. reflexivity. }
  unfold B_word. rewrite hsplit, !Str_app_assoc.
  replace (ba + 1) with (1 + ba) by lia.
  exact (rule_turnJ (npow [S1] (bc - 3) *> (S_word 0 *> (S_word 0 *> l))) r ba).
Qed.

Lemma B_word_turnJ_2 (ba : N) (l r : side) :
  CfgJ (B_word ba 2 *> l) r -->*
  CfgR (npow [S1; S0] (ba + 1) *> ([S0; S1] *> (S_word 0 *> l))) r.
Proof.
  pose proof (B_word_r2_eq ba 0 l) as h.
  replace (3 * 0 + 2) with 2 in h by lia.
  replace (0 + 1) with 1 in h by lia.
  rewrite npow_1 in h.
  rewrite h.
  replace (ba + 1) with (1 + ba) by lia.
  exact (rule_turnJ ([S0; S1] *> (S_word 0 *> l)) r ba).
Qed.

Lemma B_word_MR_calls_le (a bc used : N) (h3 : 3 * used <= bc) (l r r' : side)
  (hc : NCalls (used + 1) r r') :
  CfgR (B_word (1 + a) bc *> l) r -->*
  CfgL (B_word (1 + a) (bc - 3 * used) *> l) r'.
Proof.
  assert (hsplit : npow [S1] bc = npow [S1; S1; S1] used ++ npow [S1] (bc - 3 * used)).
  { replace bc with (used * 3 + (bc - 3 * used)) at 1 by lia.
    rewrite npow_add, <- pow_111_eq_pow_1. reflexivity. }
  unfold B_word. rewrite hsplit, !Str_app_assoc.
  exact (NCalls_from_MR used a (npow [S1] (bc - 3 * used) *> (S_word 0 *> (S_word 0 *> l))) r r' hc).
Qed.

Lemma B_word_MR_calls_gt (a q : N) (l r r' : side)
  (hc : NCalls (q + 2) r r') :
  CfgR (B_word (1 + a) (3 * q + 2) *> l) r -->*
  CfgL (npow [S1; S0] (1 + a) *> ([S0; S1] *> (S_word 0 *> l))) r'.
Proof.
  rewrite B_word_r2_eq.
  replace (q + 2) with ((q + 1) + 1) in hc by lia.
  exact (NCalls_from_MR (q + 1) a ([S0; S1] *> (S_word 0 *> l)) r r' hc).
Qed.

Lemma B_word_MR_fused (ba bc m : N) (hbc : 3 <= bc) (l r : side) :
  CfgR (B_word ba bc *> l) ([S1; S0] *> (D_word 0 *> (D_word m *> r))) -->*
  CfgR (S_word (m + 2) *> (B_word (ba + 1) (bc - 3) *> l)) ([S1; S0] *> r).
Proof.
  eapply evstep_trans; [apply (rule_defect0_D (B_word ba bc *> l) r m) |].
  eapply evstep_trans; [apply (B_word_turnJ ba bc hbc l (D_word (m + 2) *> ([S1; S0] *> r))) |].
  exact (rule_right (B_word (ba + 1) (bc - 3) *> l) ([S1; S0] *> r) (m + 2)).
Qed.


(* ========================================================================== *)
(* Section 3: Fast Symbolic Evaluator, Denotation, and Helper Specs           *)
(* ========================================================================== *)

Inductive Mode : Type := MR | ML | MJ.

Inductive WSym : Type :=
  | SD (n : N)
  | SS (n : N)
  | SB (a c : N)
  | Sb0 | Sb1 | Sw00 | Sw01 | Sw10 | Sw11 | Sw111 | Sw1101.

Inductive Run : Type := mkRun (w : WSym) (k : N).

Definition Runs : Type := list Run.

Record FastCfg : Type := mkCfg {
  cfg_mode : Mode;
  cfg_L : Runs;
  cfg_Rh : Runs;
  cfg_Rt : Runs;
  cfg_d0 : N
}.

Definition symBeq (x y : WSym) : bool :=
  match x, y with
  | SD n1, SD n2 => N.eqb n1 n2
  | SS n1, SS n2 => N.eqb n1 n2
  | SB a1 c1, SB a2 c2 => if N.eqb a1 a2 then N.eqb c1 c2 else false
  | Sb0, Sb0 => true
  | Sb1, Sb1 => true
  | Sw00, Sw00 => true
  | Sw01, Sw01 => true
  | Sw10, Sw10 => true
  | Sw11, Sw11 => true
  | Sw111, Sw111 => true
  | Sw1101, Sw1101 => true
  | _, _ => false
  end.

Definition pushRunK (w : WSym) (k : N) (xs : Runs) : Runs :=
  if N.eqb k 0 then xs
  else match xs with
  | mkRun w' k' :: xs' =>
    if symBeq w w' then mkRun w (k + k') :: xs'
    else mkRun w k :: mkRun w' k' :: xs'
  | [] => [mkRun w k]
  end.

Definition pushDK (n k : N) (xs : Runs) : Runs := pushRunK (SD n) k xs.
Definition pushSK (n k : N) (xs : Runs) : Runs := pushRunK (SS n) k xs.
Definition pushBK (a c k : N) (xs : Runs) : Runs := pushRunK (SB a c) k xs.

Definition decRunK (w : WSym) (k : N) (xs : Runs) : Runs :=
  if N.leb k 1 then xs else mkRun w (k - 1) :: xs.

Definition pushRDK (n k : N) (Rh Rt : Runs) : Runs * Runs :=
  if N.eqb k 0 then (Rh, Rt)
  else match Rh with
  | [] => ([], pushDK n k Rt)
  | _ :: _ => (pushDK n k Rh, Rt)
  end.

Fixpoint isAllDK (xs : Runs) : bool :=
  match xs with
  | [] => true
  | mkRun (SD _) _ :: rest => isAllDK rest
  | _ :: _ => false
  end.

Fixpoint flushAllDToRtK (Rh Rt : Runs) : Runs :=
  match Rh with
  | [] => Rt
  | mkRun (SD n) k :: rest => pushDK n k (flushAllDToRtK rest Rt)
  | _ :: rest => flushAllDToRtK rest Rt
  end.

Definition normRK (Rh Rt : Runs) : Runs * Runs :=
  match Rh with
  | [] => ([], Rt)
  | _ :: _ => if isAllDK Rh then ([], flushAllDToRtK Rh Rt) else (Rh, Rt)
  end.

Fixpoint isAllZeroRunsK (xs : Runs) : bool :=
  match xs with
  | [] => true
  | mkRun w k :: rest =>
    if N.eqb k 0 then isAllZeroRunsK rest
    else match w with
    | Sb0 | Sw00 => isAllZeroRunsK rest
    | _ => false
    end
  end.

Definition popBitRunsK (xs : Runs) : bool * Runs :=
  match xs with
  | [] => (false, [])
  | mkRun w k :: rest =>
    let tail := decRunK w k rest in
    match w with
    | Sb0 => (false, tail)
    | Sb1 => (true, tail)
    | Sw00 => (false, pushRunK Sb0 1 tail)
    | Sw01 => (false, pushRunK Sb1 1 tail)
    | Sw10 => (true, pushRunK Sb0 1 tail)
    | Sw11 => (true, pushRunK Sb1 1 tail)
    | Sw111 => (true, pushRunK Sw11 1 tail)
    | Sw1101 => (true, pushRunK Sb1 1 (pushRunK Sw01 1 tail))
    | SD n => (true, pushRunK Sw11 n (pushRunK Sw00 1 tail))
    | SS n => (true, pushRunK Sw01 (n + 1) tail)
    | SB a c =>
      if N.eqb a 0 then
        if N.eqb c 0 then (true, pushRunK Sw01 1 (pushRunK (SS 0) 1 tail))
        else (true, pushRunK Sb1 (c - 1) (pushRunK (SS 0) 2 tail))
      else
        (true, pushRunK Sb0 1 (pushRunK Sw10 (a - 1) (pushRunK Sb1 c (pushRunK (SS 0) 2 tail))))
    end
  end.

Definition peekBit0K (xs : Runs) : bool :=
  match xs with
  | [] => false
  | mkRun w _ :: _ =>
    match w with
    | Sb0 | Sw00 | Sw01 => false
    | _ => true
    end
  end.

Definition takeBitRunsK (b : bool) (xs : Runs) : option Runs :=
  match xs with
  | [] => if b then None else Some []
  | _ :: _ =>
    let p := peekBit0K xs in
    match b, p with
    | false, false => Some (snd (popBitRunsK xs))
    | true, true => Some (snd (popBitRunsK xs))
    | _, _ => None
    end
  end.

Definition takeBits2RunsK (b0 b1 : bool) (xs : Runs) : option Runs :=
  match takeBitRunsK b0 xs with
  | None => None
  | Some xs1 => takeBitRunsK b1 xs1
  end.

Definition takeBits5RunsK (b0 b1 b2 b3 b4 : bool) (xs : Runs) : option Runs :=
  match takeBitRunsK b0 xs with
  | None => None
  | Some xs1 =>
    match takeBitRunsK b1 xs1 with
    | None => None
    | Some xs2 =>
      match takeBitRunsK b2 xs2 with
      | None => None
      | Some xs3 =>
        match takeBitRunsK b3 xs3 with
        | None => None
        | Some xs4 => takeBitRunsK b4 xs4
        end
      end
    end
  end.

Definition takeBitRK (b : bool) (Rh Rt : Runs) (d0 : N) : option (Runs * Runs * N) :=
  match Rh with
  | [] =>
    match Rt with
    | [] =>
      if N.eqb d0 0 then
        if b then None else Some ([], [], 0)
      else
        if b then Some ([mkRun Sw00 1], [], d0 - 1) else None
    | mkRun (SD n) k :: Rt' =>
      if b then Some (pushRunK Sw11 n [mkRun Sw00 1], decRunK (SD n) k Rt', d0)
      else None
    | _ => None
    end
  | _ :: _ =>
    match takeBitRunsK b Rh with
    | None => None
    | Some Rh' => Some (Rh', Rt, d0)
    end
  end.

Definition takeBits2RK (b0 b1 : bool) (Rh Rt : Runs) (d0 : N) : option (Runs * Runs * N) :=
  match takeBitRK b0 Rh Rt d0 with
  | None => None
  | Some (Rh1, Rt1, d1) =>
    match takeBitRK b1 Rh1 Rt1 d1 with
    | None => None
    | Some (Rh2, Rt2, d2) =>
      let '(Rh3, Rt3) := normRK Rh2 Rt2 in
      Some (Rh3, Rt3, d2)
    end
  end.

Definition takeBits3RK (b0 b1 b2 : bool) (Rh Rt : Runs) (d0 : N) : option (Runs * Runs * N) :=
  match takeBitRK b0 Rh Rt d0 with
  | None => None
  | Some (Rh1, Rt1, d1) =>
    match takeBitRK b1 Rh1 Rt1 d1 with
    | None => None
    | Some (Rh2, Rt2, d2) =>
      match takeBitRK b2 Rh2 Rt2 d2 with
      | None => None
      | Some (Rh3, Rt3, d3) =>
        let '(Rh4, Rt4) := normRK Rh3 Rt3 in
        Some (Rh4, Rt4, d3)
      end
    end
  end.

Fixpoint takeOnesRunsAux (xs : Runs) (acc : N) : N * Runs :=
  match xs with
  | [] => (acc, [])
  | mkRun w k as r :: rest =>
    if N.eqb k 0 then takeOnesRunsAux rest acc
    else match w with
    | Sb1 => takeOnesRunsAux rest (acc + k)
    | Sw11 => takeOnesRunsAux rest (acc + 2 * k)
    | Sw111 => takeOnesRunsAux rest (acc + 3 * k)
    | SD n => (acc + (2 * n + 1), pushRunK Sw00 1 (decRunK w k rest))
    | SS n => (acc + 1, pushRunK Sw01 (n + 1) (decRunK w k rest))
    | Sw10 => (acc + 1, pushRunK Sb0 1 (decRunK w k rest))
    | Sw1101 => (acc + 2, pushRunK Sw01 1 (decRunK w k rest))
    | SB a c =>
      let tail := decRunK w k rest in
      if N.eqb a 0 then
        (acc + (c + 1), pushRunK Sw01 1 (pushRunK (SS 0) 1 tail))
      else
        (acc + 1, pushRunK Sb0 1 (pushRunK Sw10 (a - 1) (pushRunK Sb1 c (pushRunK (SS 0) 2 tail))))
    | _ => (acc, r :: rest)
    end
  end.

Definition takeOnesRunsK (xs : Runs) : N * Runs := takeOnesRunsAux xs 0.

Definition takeOnesRK (Rh Rt : Runs) (d0 : N) : N * Runs * Runs * N :=
  let '(c0, Rh1) := takeOnesRunsK Rh in
  match Rh1 with
  | [] =>
    match Rt with
    | mkRun (SD n) k :: Rt' =>
      (c0 + (2 * n + 1), [mkRun Sw00 1], decRunK (SD n) k Rt', d0)
    | _ =>
      if N.eqb d0 0 then (c0, [], Rt, 0)
      else (c0 + 1, [mkRun Sw00 1], Rt, d0 - 1)
    end
  | _ :: _ => (c0, Rh1, Rt, d0)
  end.

Fixpoint take10RunsAux (fuel : nat) (acc : N) (cur : Runs) : N * Runs :=
  match fuel with
  | 0%nat => (acc, cur)
  | S fuel' =>
    match cur with
    | [] => (acc, [])
    | mkRun w k :: rest =>
      if N.eqb k 0 then take10RunsAux fuel' acc rest
      else match w with
      | Sw10 => take10RunsAux fuel' (acc + k) rest
      | Sb1 =>
        if N.eqb k 1 then
          match rest with
          | mkRun nw _ :: _ =>
            match nw with
            | Sb0 | Sw00 | Sw01 =>
              let '(_, rest') := popBitRunsK rest in
              take10RunsAux fuel' (acc + 1) rest'
            | _ => (acc, mkRun Sb1 k :: rest)
            end
          | [] => (acc, mkRun Sb1 k :: rest)
          end
        else (acc, mkRun Sb1 k :: rest)
      | _ => (acc, mkRun w k :: rest)
      end
    end
  end.

Definition take10RunsK (f64 : nat) (xs : Runs) : N * Runs := take10RunsAux f64 0 xs.

Fixpoint take01RunsAux (fuel : nat) (acc : N) (cur : Runs) : N * Runs :=
  match fuel with
  | 0%nat => (acc, cur)
  | S fuel' =>
    match cur with
    | [] => (acc, [])
    | mkRun w k :: rest =>
      if N.eqb k 0 then take01RunsAux fuel' acc rest
      else match w with
      | Sw01 => take01RunsAux fuel' (acc + k) rest
      | _ =>
        match takeBits2RunsK false true cur with
        | Some cur' => take01RunsAux fuel' (acc + 1) cur'
        | None => (acc, cur)
        end
      end
    end
  end.

Definition take01RunsK (f64 : nat) (xs : Runs) : N * Runs := take01RunsAux f64 0 xs.

Fixpoint take111Prefix (xs : Runs) (acc : N) : N * Runs :=
  match xs with
  | [] => (acc, [])
  | mkRun Sw111 k :: rest => take111Prefix rest (acc + k)
  | r :: rest => (acc, r :: rest)
  end.

Definition take111RunsK (xs : Runs) : N * Runs :=
  let '(c0, xs1) := take111Prefix xs 0 in
  match xs1 with
  | [] => (c0, [])
  | mkRun w _ :: _ =>
    match w with
    | Sb0 | Sw00 | Sw01 => (c0, xs1)
    | _ =>
      let '(ones, xs2) := takeOnesRunsK xs1 in
      let q := c0 + ones / 3 in
      let r := ones mod 3 in
      if N.eqb r 0 then (q, xs2)
      else if N.eqb r 1 then (q, pushRunK Sb1 1 xs2)
      else (q, pushRunK Sw11 1 xs2)
    end
  end.

Definition tryTakeDRK (Rh Rt : Runs) (d0 : N) : option (N * Runs * Runs * N) :=
  match Rh with
  | [] =>
    match Rt with
    | mkRun (SD n) k :: Rt' => Some (n, [], decRunK (SD n) k Rt', d0)
    | _ =>
      if N.eqb d0 0 then None else Some (0, [], Rt, d0 - 1)
    end
  | mkRun (SD n) k :: Rh' =>
    let '(Rh1, Rt1) := normRK (decRunK (SD n) k Rh') Rt in
    Some (n, Rh1, Rt1, d0)
  | mkRun w _ :: _ =>
    match w with
    | Sb0 | Sw00 | Sw01 => None
    | _ =>
      let '(c1, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
      if N.eqb (N.b2n (N.odd c1)) 1 then
        match takeBits2RK false false Rh1 Rt1 d1 with
        | Some (Rh2, Rt2, d2) => Some (N.div2 c1, Rh2, Rt2, d2)
        | None => None
        end
      else None
    end
  end.

Definition tryTakeSK (f64 : nat) (L : Runs) : option (N * Runs) :=
  match L with
  | [] => None
  | mkRun (SS n) k :: rest => Some (n, decRunK (SS n) k rest)
  | mkRun Sw10 k :: rest =>
    match takeBitRunsK true rest with
    | Some rest' => Some (k - 1, rest')
    | None =>
      if N.leb k 1 then None
      else Some (k - 2, pushRunK Sb0 1 rest)
    end
  | mkRun w _ :: _ =>
    match w with
    | Sb0 | Sw00 | Sw01 => None
    | _ =>
      match takeBitRunsK true L with
      | Some L1 =>
        let '(c01, L2) := take01RunsK f64 L1 in
        if N.eqb c01 0 then None else Some (c01 - 1, L2)
      | None => None
      end
    end
  end.

Fixpoint splitDPrefixAux (Rh acc : Runs) : Runs * Runs :=
  match Rh with
  | [] => (acc, [])
  | mkRun (SD n) k :: rest => splitDPrefixAux rest (mkRun (SD n) k :: acc)
  | r :: rest => (acc, r :: rest)
  end.

Definition splitDPrefixK (Rh : Runs) : Runs * Runs := splitDPrefixAux Rh [].

Fixpoint restoreDPrefK (dpref Rh Rt : Runs) : Runs * Runs :=
  match dpref with
  | [] => (Rh, Rt)
  | mkRun (SD n) k :: rest =>
    let '(Rh', Rt') := pushRDK n k Rh Rt in
    restoreDPrefK rest Rh' Rt'
  | _ :: rest => restoreDPrefK rest Rh Rt
  end.

Definition peekHeadD3K (Rh Rt : Runs) (d0 : N) : option (N * N * Runs * Runs * N) :=
  match Rh with
  | mkRun (SD a) k :: Rh' =>
    match Rh', Rt with
    | [], [] =>
      if N.eqb a 0 then Some (0, k + d0, [], [], 0)
      else Some (a, k, Rh', [], d0)
    | _, _ => Some (a, k, Rh', Rt, d0)
    end
  | [] =>
    match Rt with
    | mkRun (SD a) k :: Rt' =>
      match Rt' with
      | [] =>
        if N.eqb a 0 then Some (0, k + d0, [], [], 0)
        else Some (a, k, [], [], d0)
      | _ :: _ => Some (a, k, [], Rt', d0)
      end
    | _ =>
      if N.eqb d0 0 then None else Some (0, d0, [], [], 0)
    end
  | _ => None
  end.

Definition popOneD3K (Rh Rt : Runs) (d0 : N) : option (N * Runs * Runs * N) :=
  match Rh with
  | mkRun (SD d) k :: Rh' => Some (d, decRunK (SD d) k Rh', Rt, d0)
  | [] =>
    match Rt with
    | mkRun (SD d) k :: Rt' => Some (d, [], decRunK (SD d) k Rt', d0)
    | _ =>
      if N.eqb d0 0 then None else Some (0, [], [], d0 - 1)
    end
  | _ => None
  end.

Definition putBackD3K (a0 rem : N) (rH1 rT1 : Runs) (d1 : N) : Runs * Runs * N :=
  match rH1, rT1 with
  | [], [] =>
    if N.eqb a0 0 then ([], [], d1 + rem)
    else let '(pRh, pRt) := pushRDK a0 rem [] [] in (pRh, pRt, d1)
  | _, _ =>
    let '(pRh, pRt) := pushRDK a0 rem rH1 rT1 in (pRh, pRt, d1)
  end.

Definition w10SplitK (rtail : Runs) : option Runs :=
  match rtail with
  | mkRun Sw10 1 :: rest => Some rest
  | mkRun Sb1 1 :: mkRun Sb0 1 :: rest => Some rest
  | _ => None
  end.

Definition doCallsRes1K (dpref : Runs) (a0 k0 h : N) (rH1 rT1 : Runs) (d1 : N) :
  option (N * Runs * Runs * N) :=
  match dpref with
  | mkRun (SD j) kj :: dp' =>
    if (if N.eqb a0 0 then N.leb 2 k0 else false) then
      let avail0 := N.div2 k0 in
      let avail := if N.leb avail0 h then avail0 else h in
      let rem := k0 - 2 * avail in
      let '(bRh, bRt, bD0) := putBackD3K a0 rem rH1 rT1 d1 in
      let bRh1 := pushRunK Sw10 1 bRh in
      let '(bRh2, bRt2) := pushRDK 2 1 bRh1 bRt in
      let '(bRh3, bRt3) := pushRDK 3 (avail - 1) bRh2 bRt2 in
      let '(bRh4, bRt4) := pushRDK (j + 1) 1 bRh3 bRt3 in
      let '(nRh, nRt) := restoreDPrefK (decRunK (SD j) kj dp') bRh4 bRt4 in
      Some (avail, nRh, nRt, bD0)
    else None
  | _ => None
  end.

Definition doCallsRes2K (dpref : Runs) (a0 k0 : N) (rH1 rT1 : Runs) (d1 : N) :
  option (N * Runs * Runs * N) :=
  match dpref with
  | mkRun (SD j) kj :: dp' =>
    if (if N.eqb a0 0 then N.eqb k0 1 else false) then
      match popOneD3K rH1 rT1 d1 with
      | Some (d, rH2, rT2, d2) =>
        let bRh1 := pushRunK Sw10 1 rH2 in
        let '(bRh2, bRt2) := pushRDK (d + 2) 1 bRh1 rT2 in
        let '(bRh3, bRt3) := pushRDK (j + 1) 1 bRh2 bRt2 in
        let '(nRh, nRt) := restoreDPrefK (decRunK (SD j) kj dp') bRh3 bRt3 in
        Some (1, nRh, nRt, d2)
      | None => None
      end
    else None
  | _ => None
  end.

Definition doCallsNoneK (Rh Rt : Runs) (d0 h : N) (allowDef : bool) : N * Runs * Runs * N :=
  let '(dpref, rtail) := splitDPrefixK Rh in
  match w10SplitK rtail with
  | None => (0, Rh, Rt, d0)
  | Some restH =>
    match peekHeadD3K restH Rt d0 with
    | None => (0, Rh, Rt, d0)
    | Some (a0, k0, rH1, rT1, d1) =>
      match doCallsRes1K dpref a0 k0 h rH1 rT1 d1 with
      | Some r => r
      | None =>
        if allowDef then
          match doCallsRes2K dpref a0 k0 rH1 rT1 d1 with
          | Some r => r
          | None =>
            if N.eqb a0 1 then
              if N.leb 2 k0 then
                let '(bRh, bRt, bD0) := putBackD3K a0 (k0 - 2) rH1 rT1 d1 in
                let bRh1 := pushRunK Sw10 1 bRh in
                let '(bRh2, bRt2) := pushRDK 2 1 bRh1 bRt in
                let '(bRh3, bRt3) := pushRDK 0 2 bRh2 bRt2 in
                let '(nRh, nRt) := restoreDPrefK dpref bRh3 bRt3 in
                (1, nRh, nRt, bD0)
              else
                match popOneD3K rH1 rT1 d1 with
                | Some (d, rH2, rT2, d2) =>
                  let bRh1 := pushRunK Sw10 1 rH2 in
                  let '(bRh2, bRt2) := pushRDK (d + 1) 1 bRh1 rT2 in
                  let '(bRh3, bRt3) := pushRDK 0 2 bRh2 bRt2 in
                  let '(nRh, nRt) := restoreDPrefK dpref bRh3 bRt3 in
                  (1, nRh, nRt, d2)
                | None => (0, Rh, Rt, d0)
                end
            else (0, Rh, Rt, d0)
          end
        else (0, Rh, Rt, d0)
      end
    end
  end.

Definition peekCollZAvailK (Rh Rt : Runs) (d0 : N) : N :=
  let '(dpref, rtail) := splitDPrefixK Rh in
  match dpref with
  | [] => 0
  | _ :: _ =>
    let afterW10 : option Runs :=
      match rtail with
      | mkRun Sw10 1 :: rest => Some rest
      | mkRun Sb1 1 :: mkRun Sb0 1 :: rest => Some rest
      | _ => None
      end in
    match afterW10 with
    | None => 0
    | Some restH =>
      match restH with
      | mkRun (SD 0) k :: restH' =>
        match restH', Rt with
        | [], [] => k + d0
        | _, _ => k
        end
      | [] =>
        match Rt with
        | mkRun (SD 0) k :: Rt' =>
          match Rt' with
          | [] => k + d0
          | _ :: _ => k
          end
        | [] => d0
        | _ => 0
        end
      | _ => 0
      end
    end
  end.

Definition hasD0AtLeastK (Rh Rt : Runs) (d0 need : N) : bool :=
  match Rh with
  | mkRun (SD n) k :: Rh' =>
    if N.eqb n 0 then
      let z := match Rh', Rt with | [], [] => k + d0 | _, _ => k end in
      N.leb need z
    else false
  | [] =>
    match Rt with
    | mkRun (SD n) k :: Rt' =>
      if N.eqb n 0 then
        let z := match Rt' with | [] => k + d0 | _ :: _ => k end in
        N.leb need z
      else false
    | [] => N.leb need d0
    | _ => false
    end
  | _ => false
  end.

Fixpoint runDtailLoopAux (fuel : nat) (did : bool) (m : Mode) (L Rt : Runs) (d : N) : option FastCfg :=
  match fuel with
  | 0%nat => if did then Some (mkCfg m L [] Rt d) else None
  | S fuel' =>
    match L with
    | [] => if did then Some (mkCfg m [] [] Rt d) else None
    | mkRun (SS n) k :: L' =>
      match m with
      | ML => runDtailLoopAux fuel' true ML L' (pushDK n k Rt) d
      | MJ => runDtailLoopAux fuel' true ML (decRunK (SS n) k L') (pushDK (n + 1) 1 Rt) d
      | MR => if did then Some (mkCfg m L [] Rt d) else None
      end
    | mkRun (SB a c) k :: L' =>
      if N.leb 1 a then
        let r := c mod 3 in
        let qv := c / 3 in
        match m with
        | MJ =>
          if N.eqb r 2 then
            let nd := d + 2 * (k * (qv + 1)) in
            runDtailLoopAux fuel' true MJ L' (pushDK (a + 1) k Rt) nd
          else if N.leb 3 c then
            let L1 := decRunK (SB a c) k L' in
            let nd := d + 2 * qv in
            let Rt1 := if N.eqb r 0 then pushDK 0 1 (pushDK (a + 1) 1 Rt)
                       else pushDK 0 2 (pushDK a 1 Rt) in
            runDtailLoopAux fuel' true ML L1 Rt1 nd
          else if did then Some (mkCfg m L [] Rt d) else None
        | ML =>
          if N.eqb r 2 then
            let nd := d + 2 * (k * (qv + 1)) in
            let Rt1 := pushDK (a + 1) (k - 1) (pushDK a 1 Rt) in
            runDtailLoopAux fuel' true MJ L' Rt1 nd
          else
            let L1 := decRunK (SB a c) k L' in
            let nd := d + 2 * qv in
            let Rt1 := if N.eqb r 0 then pushDK 0 1 (pushDK a 1 Rt)
                       else pushDK 0 2 (pushDK (a - 1) 1 Rt) in
            runDtailLoopAux fuel' true ML L1 Rt1 nd
        | MR => if did then Some (mkCfg m L [] Rt d) else None
        end
      else if did then Some (mkCfg m L [] Rt d) else None
    | _ => if did then Some (mkCfg m L [] Rt d) else None
    end
  end.

Definition runDtailLoopK (f4096 : nat) (m0 : Mode) (L0 Rt0 : Runs) (d0 : N) : option FastCfg :=
  runDtailLoopAux f4096 false m0 L0 Rt0 d0.

Definition stopMr (did : bool) (L Rh Rt : Runs) (d : N) : option FastCfg :=
  if did then Some (mkCfg MR L (pushRunK Sw10 1 Rh) Rt d) else None.

Definition stepMrW10WithD
  (go : bool -> Runs -> Runs -> Runs -> N -> option FastCfg)
  (did : bool) (L Rh Rt : Runs) (d : N)
  (a ka : N) (Rh1 Rt1 : Runs) (d1 : N) (isRh : bool) : option FastCfg :=
  if (if N.leb 2 a then N.leb 2 ka else false) then
    let kp := N.div2 ka in
    let rem := N.b2n (N.odd ka) in
    let '(RhN, RtN) := if isRh then (pushDK a rem Rh1, Rt1) else (Rh1, pushDK a rem Rt1) in
    go true (pushBK (a + 2) (2 * (a - 2)) kp L) RhN RtN d1
  else if N.eqb ka 1 then
    match popOneD3K Rh1 Rt1 d1 with
    | None => stopMr did L Rh Rt d
    | Some (m, Rh2, Rt2, d2) =>
      if N.eqb a 0 then
        let fused : option FastCfg :=
          match L with
          | mkRun (SB ba bc) bk :: L' =>
            if (if N.leb 1 ba then N.leb 3 bc else false) then
              let canColl :=
                if N.eqb (bc mod 3) 2 then hasD0AtLeastK Rh2 Rt2 d2 (2 * (bc / 3 + 1))
                else false in
              if canColl then None
              else
                let L1 := pushSK (m + 2) 1 (pushBK (ba + 1) (bc - 3) 1 (decRunK (SB ba bc) bk L')) in
                go true L1 Rh2 Rt2 d2
            else None
          | _ => None
          end in
        match fused with
        | Some cfg => Some cfg
        | None =>
          let Rh3 := pushRunK Sw10 1 Rh2 in
          let '(Rh4, Rt4) := pushRDK (m + 2) 1 Rh3 Rt2 in
          Some (mkCfg MJ L Rh4 Rt4 d2)
        end
      else if N.eqb a 1 then
        let Rh3 := pushRunK Sw10 1 Rh2 in
        let '(Rh4, Rt4) := pushRDK (m + 1) 1 Rh3 Rt2 in
        let '(Rh5, Rt5) := pushRDK 0 2 Rh4 Rt4 in
        Some (mkCfg ML L Rh5 Rt5 d2)
      else
        go true (pushBK (m + 2) (2 * (a - 2)) 1 L) Rh2 Rt2 d2
    end
  else stopMr did L Rh Rt d.

Fixpoint runMrW10LoopAux (fuel : nat) (did : bool) (L Rh Rt : Runs) (d : N) : option FastCfg :=
  match fuel with
  | 0%nat => stopMr did L Rh Rt d
  | S fuel' =>
    match Rh with
    | mkRun (SD a) ka :: Rh1 =>
      stepMrW10WithD (runMrW10LoopAux fuel') did L Rh Rt d a ka Rh1 Rt d true
    | [] =>
      match Rt with
      | mkRun (SD a) ka :: Rt1 =>
        stepMrW10WithD (runMrW10LoopAux fuel') did L Rh Rt d a ka [] Rt1 d false
      | _ =>
        if N.eqb d 0 then stopMr did L Rh Rt d
        else stepMrW10WithD (runMrW10LoopAux fuel') did L Rh Rt d 0 d [] [] 0 false
      end
    | _ => stopMr did L Rh Rt d
    end
  end.

Definition runMrW10LoopK (f4096 : nat) (L0 Rh0 Rt0 : Runs) (d0 : N) : option FastCfg :=
  match Rh0 with
  | mkRun Sw10 1 :: rest0 =>
    let hasD :=
      match rest0 with
      | mkRun (SD _) _ :: _ => true
      | [] =>
        match Rt0 with
        | _ :: _ => true
        | [] => negb (N.eqb d0 0)
        end
      | _ => false
      end in
    if hasD then runMrW10LoopAux f4096 false L0 rest0 Rt0 d0 else None
  | _ => None
  end.

Fixpoint sweepDK (L Rh : Runs) : Runs * Runs :=
  match Rh with
  | [] => (L, [])
  | mkRun (SD n) k :: rest => sweepDK (pushSK n k L) rest
  | r :: rest => (L, r :: rest)
  end.

Fixpoint sweepSK (L Rh Rt : Runs) : Runs * Runs * Runs :=
  match L with
  | [] => ([], Rh, Rt)
  | mkRun (SS n) k :: rest =>
    let '(Rh', Rt') := pushRDK n k Rh Rt in
    sweepSK rest Rh' Rt'
  | r :: rest => (r :: rest, Rh, Rt)
  end.

Definition stepMRK (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) : option FastCfg :=
  match Rh with
  | [] =>
    let '(b1, L1) := take10RunsK f64 L in
    if N.eqb b1 0 then Some (mkCfg ML L [] Rt (d0 + 2))
    else
      let '(c111, L2) := take111RunsK L1 in
      Some (mkCfg ML (pushRunK Sw10 b1 L2) [] Rt (d0 + 2 * (c111 + 1)))
  | _ :: _ =>
    match runMrW10LoopK f4096 L Rh Rt d0 with
    | Some cfg => Some cfg
    | None =>
      match Rh with
      | mkRun (SD _) _ :: _ =>
        let callRes : option FastCfg :=
          match L with
          | mkRun (SB ba bc) bk :: L' =>
            if N.leb 1 ba then
              let c111av := bc / 3 + (if N.eqb (bc mod 3) 2 then 1 else 0) in
              let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 (c111av + 1) true in
              if N.eqb hd 0 then None
              else
                let used := hd - 1 in
                let L1 := decRunK (SB ba bc) bk L' in
                let L2 :=
                  if N.leb (3 * used) bc then pushBK ba (bc - 3 * used) 1 L1
                  else pushRunK Sw10 ba (pushRunK Sw01 1 (pushRunK (SS 0) 1 L1)) in
                Some (mkCfg ML L2 nRh nRt nD0)
            else None
          | _ =>
            let '(b1, L1) := take10RunsK f64 L in
            if N.eqb b1 0 then None
            else
              let '(c111, L2) := take111RunsK L1 in
              let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 (c111 + 1) true in
              if N.eqb hd 0 then None
              else
                let rem := c111 - (hd - 1) in
                Some (mkCfg ML (pushRunK Sw10 b1 (pushRunK Sw111 rem L2)) nRh nRt nD0)
          end in
        match callRes with
        | Some cfg => Some cfg
        | None =>
          let '(L', Rh') := sweepDK L Rh in
          Some (mkCfg MR L' Rh' Rt d0)
        end
      | _ =>
        let '(c10, Rh1a) := take10RunsK f64 Rh in
        let res10 : option FastCfg :=
          if N.eqb c10 0 then None
          else
            let '(Rh1, Rt1) := normRK Rh1a Rt in
            if N.eqb (N.b2n (N.odd c10)) 1 then
              let odd3 : option FastCfg :=
                if N.eqb c10 3 then
                  match tryTakeDRK Rh1 Rt1 d0 with
                  | Some (dn, Rh2, Rt2, d2) =>
                    let L' := pushRunK Sw11 dn (pushRunK Sw1101 2 (pushRunK (SS 0) 1 L)) in
                    Some (mkCfg ML L' (pushRunK Sb1 1 Rh2) Rt2 d2)
                  | None => None
                  end
                else None in
              match odd3 with
              | Some cfg => Some cfg
              | None =>
                let Rh1' := pushRunK Sw10 (c10 - 1) Rh1 in
                match tryTakeDRK Rh1' Rt1 d0 with
                | None => None
                | Some (a, Rh2, Rt2, d2) =>
                  match tryTakeDRK Rh2 Rt2 d2 with
                  | Some (m, Rh3, Rt3, d3) =>
                    if N.eqb a 0 then
                      let Rh4 := pushRunK Sw10 1 Rh3 in
                      let '(Rh5, Rt5) := pushRDK (m + 2) 1 Rh4 Rt3 in
                      Some (mkCfg MJ L Rh5 Rt5 d3)
                    else if N.eqb a 1 then None
                    else
                      Some (mkCfg MR (pushBK (m + 2) (2 * (a - 2)) 1 L) (pushRunK Sw10 1 Rh3) Rt3 d3)
                  | None =>
                    match takeBits2RK false false Rh2 Rt2 d2 with
                    | Some (Rh3, Rt3, d3) =>
                      if N.eqb a 0 then
                        let L' := pushRunK Sw10 1 (pushRunK Sw01 1 (pushRunK (SS 0) 1 L)) in
                        Some (mkCfg MR L' Rh3 Rt3 d3)
                      else None
                    | None =>
                      if N.leb 1 a then
                        let '(ones, Rh3, Rt3, d3) := takeOnesRK Rh2 Rt2 d2 in
                        if N.eqb (N.b2n (N.odd ones)) 1 then
                          match takeBitRK false Rh3 Rt3 d3 with
                          | Some (Rh4, Rt4, d4) =>
                            let mv := N.div2 ones in
                            if N.eqb a 1 then
                              let Rh5 := pushRunK Sb1 1 Rh4 in
                              let '(Rh6, Rt6) := pushRDK (mv + 1) 1 Rh5 Rt4 in
                              let '(Rh7, Rt7) := pushRDK 0 2 Rh6 Rt6 in
                              Some (mkCfg ML L Rh7 Rt7 d4)
                            else
                              Some (mkCfg MR (pushBK (mv + 2) (2 * (a - 2)) 1 L) (pushRunK Sb1 1 Rh4) Rt4 d4)
                          | None => None
                          end
                        else None
                      else None
                    end
                  end
                end
              end
            else
              match tryTakeDRK Rh1 Rt1 d0 with
              | Some (dn, Rh2, Rt2, d2) =>
                let kp := N.div2 c10 in
                let L' := pushRunK Sw10 dn (pushRunK Sw1101 kp (pushRunK (SS 0) 1 L)) in
                Some (mkCfg MR L' Rh2 Rt2 d2)
              | None =>
                if N.eqb c10 2 then
                  let '(ones, Rh2, Rt2, d2) := takeOnesRK Rh1 Rt1 d0 in
                  if N.eqb (N.b2n (N.odd ones)) 0 then
                    match takeBits2RK false false Rh2 Rt2 d2 with
                    | Some (Rh3, Rt3, d3) =>
                      let m := N.div2 ones in
                      let L' := pushRunK Sw10 m (pushRunK Sw1101 1 (pushRunK (SS 0) 1 L)) in
                      Some (mkCfg ML L' (pushRunK Sw10 1 Rh3) Rt3 d3)
                    | None => None
                    end
                  else None
                else None
              end in
        match res10 with
        | Some cfg => Some cfg
        | None =>
          match tryTakeDRK Rh Rt d0 with
          | Some (dn, Rh', Rt', d') => Some (mkCfg MR (pushSK dn 1 L) Rh' Rt' d')
          | None =>
            let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
            let evenRes : option FastCfg :=
              if (if N.leb 2 ones then N.eqb (N.b2n (N.odd ones)) 0 else false) then
                match takeBits2RK false false Rh1 Rt1 d1 with
                | Some (Rh2, Rt2, d2) =>
                  let Rh3 := pushRunK Sw10 1 Rh2 in
                  let '(Rh4, Rt4) := pushRDK (N.div2 ones) 1 Rh3 Rt2 in
                  Some (mkCfg ML L Rh4 Rt4 d2)
                | None => None
                end
              else None in
            match evenRes with
            | Some cfg => Some cfg
            | None =>
              match takeBits3RK true true false Rh Rt d0 with
              | Some (Rh', Rt', d') => Some (mkCfg ML (pushRunK (SS 1) 1 L) (pushRunK Sb1 1 Rh') Rt' d')
              | None => None
              end
            end
          end
        end
      end
    end
  end.

Definition stepMLK (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) : option FastCfg :=
  let tryDtail : option FastCfg :=
    match Rh with
    | [] => runDtailLoopK f4096 ML L Rt d0
    | _ :: _ => None
    end in
  match tryDtail with
  | Some cfg => Some cfg
  | None =>
    match L with
    | mkRun (SS _) _ :: _ =>
      let '(L', Rh', Rt') := sweepSK L Rh Rt in
      Some (mkCfg ML L' Rh' Rt' d0)
    | mkRun (SB ba bc) bk :: L' =>
      let tryColl : option FastCfg :=
        match Rh with
        | [] => None
        | _ :: _ =>
          if (if N.eqb (bc mod 3) 2 then N.leb 1 ba else false) then
            let stepH := bc / 3 + 1 in
            let zAv := peekCollZAvailK Rh Rt d0 in
            let av := (N.div2 zAv) / stepH in
            let mc := if N.leb bk av then bk else av in
            if N.eqb mc 0 then None
            else
              let need := mc * stepH in
              let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 need false in
              if N.eqb hd need then
                let L1 := if N.eqb bk mc then L' else mkRun (SB ba bc) (bk - mc) :: L' in
                let '(nRh1, nRt1) := pushRDK ba 1 nRh nRt in
                let '(nRh2, nRt2) := pushRDK (ba + 1) (mc - 1) nRh1 nRt1 in
                Some (mkCfg MJ L1 nRh2 nRt2 nD0)
              else None
          else None
        end in
      match tryColl with
      | Some cfg => Some cfg
      | None =>
        let L1 := decRunK (SB ba bc) bk L' in
        let L2 := pushRunK Sw10 ba (pushRunK Sb1 bc (pushRunK (SS 0) 2 L1)) in
        Some (mkCfg ML L2 Rh Rt d0)
      end
    | _ =>
      let '(b1, L1) := take10RunsK f64 L in
      let res10 : option FastCfg :=
        if N.eqb b1 0 then None
        else
          let '(c111, L2) := take111RunsK L1 in
          if N.eqb c111 0 then
            match takeBits5RunsK false true true false true L2 with
            | Some L3 =>
              let '(Rh1, Rt1) := pushRDK b1 1 Rh Rt in
              Some (mkCfg MJ L3 Rh1 Rt1 d0)
            | None =>
              let over2 : option FastCfg :=
                match takeBits2RunsK true true L2 with
                | Some L3 =>
                  if isAllZeroRunsK L3 then
                    Some (mkCfg MR (pushRunK Sw10 2 (pushRunK Sw11 b1 [])) (pushRunK Sb1 1 Rh) Rt d0)
                  else None
                | None => None
                end in
              match over2 with
              | Some cfg => Some cfg
              | None =>
                match takeBitRunsK true L2 with
                | Some L3 =>
                  if isAllZeroRunsK L3 then
                    match tryTakeDRK Rh Rt d0 with
                    | Some (dn, Rh', Rt', d') =>
                      Some (mkCfg MR (pushRunK Sw10 (dn + 2) (pushRunK Sw11 (b1 - 1) [])) (pushRunK Sw10 1 Rh') Rt' d')
                    | None => None
                    end
                  else None
                | None => None
                end
              end
            end
          else
            match Rh with
            | [] => Some (mkCfg ML (pushRunK Sw10 b1 L2) [] Rt (d0 + 2 * c111))
            | _ :: _ =>
              let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 c111 true in
              if N.eqb hd 0 then
                Some (mkCfg MR (pushRunK Sw10 b1 (pushRunK Sw111 (c111 - 1) L2)) Rh Rt d0)
              else
                Some (mkCfg ML (pushRunK Sw10 b1 (pushRunK Sw111 (c111 - hd) L2)) nRh nRt nD0)
            end in
      match res10 with
      | Some cfg => Some cfg
      | None =>
        match tryTakeSK f64 L with
        | Some (sn, L') =>
          let '(Rh1, Rt1) := pushRDK sn 1 Rh Rt in
          Some (mkCfg ML L' Rh1 Rt1 d0)
        | None =>
          let turnB : option FastCfg :=
            match takeBits2RunsK true true L with
            | Some L' =>
              match tryTakeDRK Rh Rt d0 with
              | Some (dn, Rh', Rt', d') => Some (mkCfg MR (pushRunK Sw10 (dn + 1) L') Rh' Rt' d')
              | None =>
                let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
                if N.eqb (N.b2n (N.odd ones)) 0 then
                  match takeBitRK false Rh1 Rt1 d1 with
                  | Some (Rh2, Rt2, d2) =>
                    Some (mkCfg ML (pushRunK Sw10 (N.div2 ones + 1) L') (pushRunK Sb1 1 Rh2) Rt2 d2)
                  | None => None
                  end
                else None
              end
            | None => None
            end in
          match turnB with
          | Some cfg => Some cfg
          | None =>
            let '(k01, L') := take01RunsK f64 L in
            if N.eqb k01 0 then
              match takeBits2RunsK true false L with
              | Some L' => Some (mkCfg MJ L' Rh Rt d0)
              | None =>
                if isAllZeroRunsK L then
                  let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
                  match takeBits2RK false false Rh1 Rt1 d1 with
                  | Some (Rh2, Rt2, d2) =>
                    Some (mkCfg ML (pushRunK Sb1 (ones + 4) []) (pushRunK Sb1 1 Rh2) Rt2 d2)
                  | None => None
                  end
                else None
              end
            else
              match Rh with
              | mkRun (SD dn) kd :: Rh' =>
                let '(Rh1, Rt1) := pushRDK (dn + k01) 1 (decRunK (SD dn) kd Rh') Rt in
                Some (mkCfg ML L' Rh1 Rt1 d0)
              | [] =>
                match Rt with
                | mkRun (SD dn) kd :: Rt' =>
                  Some (mkCfg ML L' [] (pushDK (dn + k01) 1 (decRunK (SD dn) kd Rt')) d0)
                | [] =>
                  if N.eqb d0 0 then Some (mkCfg ML L' (pushRunK Sw11 k01 []) [] 0)
                  else Some (mkCfg ML L' [] [mkRun (SD k01) 1] (d0 - 1))
                | _ => Some (mkCfg ML L' (pushRunK Sw11 k01 []) Rt d0)
                end
              | _ => Some (mkCfg ML L' (pushRunK Sw11 k01 Rh) Rt d0)
              end
            end
          end
        end
    end
  end.

Definition stepMJK (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) : option FastCfg :=
  let tryDtail : option FastCfg :=
    match Rh with
    | [] => runDtailLoopK f4096 MJ L Rt d0
    | _ :: _ => None
    end in
  match tryDtail with
  | Some cfg => Some cfg
  | None =>
    match L with
    | mkRun (SB ba bc) bk :: L' =>
      let tryColl : option FastCfg :=
        match Rh with
        | [] => None
        | _ :: _ =>
          if (if N.eqb (bc mod 3) 2 then N.leb 1 ba else false) then
            let stepH := bc / 3 + 1 in
            let zAv := peekCollZAvailK Rh Rt d0 in
            let av := (N.div2 zAv) / stepH in
            let mc := if N.leb bk av then bk else av in
            if N.eqb mc 0 then None
            else
              let need := mc * stepH in
              let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 need false in
              if N.eqb hd need then
                let L1 := if N.eqb bk mc then L' else mkRun (SB ba bc) (bk - mc) :: L' in
                let '(nRh1, nRt1) := pushRDK (ba + 1) mc nRh nRt in
                Some (mkCfg MJ L1 nRh1 nRt1 nD0)
              else None
          else None
        end in
      match tryColl with
      | Some cfg => Some cfg
      | None =>
        if (if N.leb 1 ba then N.leb 3 bc else false) then
          let L1 := decRunK (SB ba bc) bk L' in
          Some (mkCfg MR (pushBK (ba + 1) (bc - 3) 1 L1) Rh Rt d0)
        else if (if N.leb 1 ba then N.eqb bc 2 else false) then
          let L1 := decRunK (SB ba bc) bk L' in
          let L2 := pushRunK Sw10 (ba + 1) (pushRunK Sw01 1 (pushRunK (SS 0) 1 L1)) in
          Some (mkCfg MR L2 Rh Rt d0)
        else
          let L1 := decRunK (SB ba bc) bk L' in
          let L2 := pushRunK Sw10 ba (pushRunK Sb1 bc (pushRunK (SS 0) 2 L1)) in
          Some (mkCfg MJ L2 Rh Rt d0)
      end
    | _ =>
      match tryTakeSK f64 L with
      | Some (sn, L') =>
        let '(Rh1, Rt1) := pushRDK (sn + 1) 1 Rh Rt in
        Some (mkCfg ML L' Rh1 Rt1 d0)
      | None =>
        if isAllZeroRunsK L then
          Some (mkCfg ML (pushRunK Sw111 1 []) (pushRunK Sb1 1 Rh) Rt d0)
        else None
      end
    end
  end.

Definition stepK (f64 f4096 : nat) (c : FastCfg) : option FastCfg :=
  match cfg_mode c with
  | MR => stepMRK f64 f4096 (cfg_L c) (cfg_Rh c) (cfg_Rt c) (cfg_d0 c)
  | ML => stepMLK f64 f4096 (cfg_L c) (cfg_Rh c) (cfg_Rt c) (cfg_d0 c)
  | MJ => stepMJK f64 f4096 (cfg_L c) (cfg_Rh c) (cfg_Rt c) (cfg_d0 c)
  end.

Definition stepOpt (f64 f4096 : nat) (st : option FastCfg) : option FastCfg :=
  match st with
  | Some cfg => stepK f64 f4096 cfg
  | None => None
  end.

Definition isHaltedK (c : FastCfg) : bool :=
  match cfg_mode c with
  | ML =>
    match takeBits5RunsK false false true true true (cfg_L c) with
    | Some _ => true
    | None => false
    end
  | _ => false
  end.

Definition cp_0 : FastCfg := mkCfg ML [mkRun Sb1 1] [mkRun Sb1 1] [] 0.

Definition runHalted (p : positive) (c : FastCfg) : bool :=
  let f64 := Nat.pow 2 6 in
  let f4096 := Nat.pow 2 12 in
  match Pos.iter (stepOpt f64 f4096) (Some c) p with
  | Some cfg => isHaltedK cfg
  | None => false
  end.

(* Denotation and Validity *)

Definition bitSym (b : bool) : Sym := if b then S1 else S0.

Definition evalSym (w : WSym) : list Sym :=
  match w with
  | SD n => D_word n
  | SS n => S_word n
  | SB a c => B_word a c
  | Sb0 => [S0]
  | Sb1 => [S1]
  | Sw00 => [S0; S0]
  | Sw01 => [S0; S1]
  | Sw10 => [S1; S0]
  | Sw11 => [S1; S1]
  | Sw111 => [S1; S1; S1]
  | Sw1101 => [S1; S1; S0; S1]
  end.

Fixpoint evalRuns (xs : Runs) (tail : side) : side :=
  match xs with
  | [] => tail
  | mkRun w k :: rest => npow (evalSym w) k *> evalRuns rest tail
  end.

Definition evalR (Rh Rt : Runs) (d0 : N) : side :=
  evalRuns Rh (evalRuns Rt (npow (D_word 0) d0 *> 0inf)).

Definition evalCfg (c : FastCfg) : Q * tape :=
  match cfg_mode c with
  | MR => CfgR (evalRuns (cfg_L c) 0inf) (evalR (cfg_Rh c) (cfg_Rt c) (cfg_d0 c))
  | ML => CfgL (evalRuns (cfg_L c) 0inf) (evalR (cfg_Rh c) (cfg_Rt c) (cfg_d0 c))
  | MJ => CfgJ (evalRuns (cfg_L c) 0inf) (evalR (cfg_Rh c) (cfg_Rt c) (cfg_d0 c))
  end.

Fixpoint AllPos (xs : Runs) : Prop :=
  match xs with
  | [] => True
  | mkRun _ k :: rest => 1 <= k /\ AllPos rest
  end.

Fixpoint AllD (xs : Runs) : Prop :=
  match xs with
  | [] => True
  | mkRun (SD _) _ :: rest => AllD rest
  | mkRun _ _ :: _ => False
  end.

Definition ValidCfg (c : FastCfg) : Prop :=
  AllPos (cfg_L c) /\ AllPos (cfg_Rh c) /\ AllPos (cfg_Rt c) /\ AllD (cfg_Rt c).

Ltac split_and := repeat match goal with |- _ /\ _ => split end.

Lemma symBeq_eq (a b : WSym) (h : symBeq a b = true) : a = b.
Proof.
  destruct a, b; simpl in h; try discriminate.
  - apply N.eqb_eq in h; subst; reflexivity.
  - apply N.eqb_eq in h; subst; reflexivity.
  - destruct (N.eqb a a0) eqn:ha; [| discriminate].
    apply N.eqb_eq in ha; apply N.eqb_eq in h; subst; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma evalRuns_append (xs ys : Runs) (tail : side) :
  evalRuns (xs ++ ys) tail = evalRuns xs (evalRuns ys tail).
Proof.
  induction xs as [| [w k] rest ih]; simpl; [reflexivity | rewrite ih; reflexivity].
Qed.

Lemma AllPos_append {xs ys : Runs} (hx : AllPos xs) (hy : AllPos ys) :
  AllPos (xs ++ ys).
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact hy | exact (conj (proj1 hx) (ih (proj2 hx)))].
Qed.

Lemma AllD_append {xs ys : Runs} (hx : AllD xs) (hy : AllD ys) :
  AllD (xs ++ ys).
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact hy |].
  destruct w; try contradiction; exact (ih hx).
Qed.

Lemma AllPos_rev {xs : Runs} (h : AllPos xs) : AllPos (rev xs).
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact I |].
  apply AllPos_append; [exact (ih (proj2 h)) | simpl; exact (conj (proj1 h) I)].
Qed.

Lemma AllD_rev {xs : Runs} (h : AllD xs) : AllD (rev xs).
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact I |].
  destruct w; try contradiction.
  apply AllD_append; [exact (ih h) | exact I].
Qed.

Lemma evalRuns_pushRunK (w : WSym) (k : N) (xs : Runs) (tail : side) :
  evalRuns (pushRunK w k xs) tail = npow (evalSym w) k *> evalRuns xs tail.
Proof.
  unfold pushRunK.
  destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst k. rewrite npow_0; reflexivity.
  - destruct xs as [| [w' k'] rest]; [reflexivity |].
    destruct (symBeq w w') eqn:hw; [| reflexivity].
    apply symBeq_eq in hw; subst w'.
    simpl. rewrite npow_append_npow. reflexivity.
Qed.

Lemma AllPos_pushRunK (w : WSym) (k : N) {xs : Runs} (hpos : AllPos xs) :
  AllPos (pushRunK w k xs).
Proof.
  unfold pushRunK.
  destruct (N.eqb k 0) eqn:hk; [exact hpos |].
  apply N.eqb_neq in hk.
  destruct xs as [| [w' k'] rest].
  - simpl; split; [lia | exact I].
  - destruct (symBeq w w').
    + simpl in *; split; [lia | exact (proj2 hpos)].
    + simpl in *; split; [lia | exact hpos].
Qed.

Lemma AllD_pushDK (n k : N) {xs : Runs} (hD : AllD xs) : AllD (pushDK n k xs).
Proof.
  unfold pushDK, pushRunK.
  destruct (N.eqb k 0); [exact hD |].
  destruct xs as [| [w' k'] rest]; [exact I |].
  destruct (symBeq (SD n) w'); simpl in *; [| exact hD].
  destruct w'; try contradiction; exact hD.
Qed.

Lemma evalRuns_pushDK (n k : N) (xs : Runs) (tail : side) :
  evalRuns (pushDK n k xs) tail = npow (D_word n) k *> evalRuns xs tail.
Proof. exact (evalRuns_pushRunK (SD n) k xs tail). Qed.

Lemma evalRuns_pushSK (n k : N) (xs : Runs) (tail : side) :
  evalRuns (pushSK n k xs) tail = npow (S_word n) k *> evalRuns xs tail.
Proof. exact (evalRuns_pushRunK (SS n) k xs tail). Qed.

Lemma evalRuns_pushBK (a c k : N) (xs : Runs) (tail : side) :
  evalRuns (pushBK a c k xs) tail = npow (B_word a c) k *> evalRuns xs tail.
Proof. exact (evalRuns_pushRunK (SB a c) k xs tail). Qed.

Lemma AllPos_pushDK (n k : N) {xs : Runs} (h : AllPos xs) : AllPos (pushDK n k xs).
Proof. exact (AllPos_pushRunK (SD n) k h). Qed.

Lemma AllPos_pushSK (n k : N) {xs : Runs} (h : AllPos xs) : AllPos (pushSK n k xs).
Proof. exact (AllPos_pushRunK (SS n) k h). Qed.

Lemma AllPos_pushBK (a c k : N) {xs : Runs} (h : AllPos xs) : AllPos (pushBK a c k xs).
Proof. exact (AllPos_pushRunK (SB a c) k h). Qed.

Lemma evalRuns_decRunK (w : WSym) (k : N) (xs : Runs) (tail : side) (hk : 1 <= k) :
  evalSym w *> evalRuns (decRunK w k xs) tail = npow (evalSym w) k *> evalRuns xs tail.
Proof.
  unfold decRunK.
  destruct (N.leb k 1) eqn:hle.
  - apply N.leb_le in hle. replace k with 1 by lia.
    rewrite npow_1. reflexivity.
  - apply N.leb_gt in hle. simpl.
    replace k with (1 + (k - 1)) at 2 by lia.
    rewrite npow_one_add, Str_app_assoc. reflexivity.
Qed.

Lemma AllPos_decRunK (w : WSym) (k : N) {xs : Runs} (hpos : AllPos xs) :
  AllPos (decRunK w k xs).
Proof.
  unfold decRunK.
  destruct (N.leb k 1) eqn:hle; [exact hpos |].
  apply N.leb_gt in hle. simpl; split; [lia | exact hpos].
Qed.

Lemma AllD_decRunK (n k : N) {xs : Runs} (hD : AllD (mkRun (SD n) k :: xs)) :
  AllD (decRunK (SD n) k xs).
Proof.
  simpl in hD. unfold decRunK. destruct (N.leb k 1); exact hD.
Qed.

Lemma pushRDK_spec (n k : N) (Rh Rt : Runs) (d0 : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt) :
  let '(Rh', Rt') := pushRDK n k Rh Rt in
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  evalR Rh' Rt' d0 = npow (D_word n) k *> evalR Rh Rt d0.
Proof.
  unfold pushRDK.
  destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst k.
    exact (conj hRh (conj hRt (conj hD eq_refl))).
  - destruct Rh as [| r rest].
    + split_and; [exact I | exact (AllPos_pushDK n k hRt) | exact (AllD_pushDK n k hD) |].
      unfold evalR; simpl. rewrite evalRuns_pushDK. reflexivity.
    + split_and; [exact (AllPos_pushDK n k hRh) | exact hRt | exact hD |].
      unfold evalR. rewrite evalRuns_pushDK. reflexivity.
Qed.

Lemma isAllDK_spec {xs : Runs} (h : isAllDK xs = true) : AllD xs.
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact I |].
  destruct w; try discriminate; exact (ih h).
Qed.

Lemma flushAllDToRtK_spec (Rh Rt : Runs) (tail : side)
  (hRh : AllPos Rh) (hDRh : AllD Rh) (hRt : AllPos Rt) (hDRt : AllD Rt) :
  AllPos (flushAllDToRtK Rh Rt) /\ AllD (flushAllDToRtK Rh Rt) /\
  evalRuns (flushAllDToRtK Rh Rt) tail = evalRuns Rh (evalRuns Rt tail).
Proof.
  induction Rh as [| [w k] rest ih]; simpl in *.
  - exact (conj hRt (conj hDRt eq_refl)).
  - destruct w; try contradiction.
    destruct (ih (proj2 hRh) hDRh) as [hp [hd he]].
    split_and; [exact (AllPos_pushDK n k hp) | exact (AllD_pushDK n k hd) |].
    rewrite evalRuns_pushDK, he. reflexivity.
Qed.

Lemma normRK_spec (Rh Rt : Runs) (d0 : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt) :
  let '(Rh', Rt') := normRK Rh Rt in
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\ evalR Rh' Rt' d0 = evalR Rh Rt d0.
Proof.
  unfold normRK.
  destruct Rh as [| r rest]; [exact (conj I (conj hRt (conj hD eq_refl))) |].
  destruct (isAllDK (r :: rest)) eqn:had; [| exact (conj hRh (conj hRt (conj hD eq_refl)))].
  destruct (flushAllDToRtK_spec (r :: rest) Rt (npow (D_word 0) d0 *> 0inf) hRh (isAllDK_spec had) hRt hD)
    as [hp [hd he]].
  exact (conj I (conj hp (conj hd he))).
Qed.

Lemma isAllZeroRunsK_spec {xs : Runs} (h : isAllZeroRunsK xs = true) :
  evalRuns xs 0inf = 0inf.
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [reflexivity |].
  destruct (N.eqb k 0) eqn:hk.
  - apply N.eqb_eq in hk; subst k. rewrite npow_0, (ih h). reflexivity.
  - destruct w; try discriminate.
    + unfold evalSym; rewrite (ih h). apply zeros_append_default.
    + unfold evalSym; rewrite (ih h). change [S0; S0] with ([S0] ++ [S0]).
      rewrite <- npow_mul_two. apply zeros_append_default.
Qed.

Lemma popBitRunsK_spec (r : Run) (rest : Runs) (tail : side) (hpos : AllPos (r :: rest)) :
  let '(b, xs') := popBitRunsK (r :: rest) in
  b = peekBit0K (r :: rest) /\ AllPos xs' /\
  evalRuns (r :: rest) tail = bitSym b >> evalRuns xs' tail.
Proof.
  destruct r as [w k].
  destruct hpos as [hk hrest].
  pose proof (evalRuns_decRunK w k rest tail hk) as hdec.
  pose proof (AllPos_decRunK w k hrest) as hposDec.
  simpl popBitRunsK; simpl peekBit0K.
  destruct w as [n | n | a c | | | | | | | |]; cbn [popBitRunsK peekBit0K].
  - split_and; [reflexivity | exact (AllPos_pushRunK Sw11 n (AllPos_pushRunK Sw00 1 hposDec)) |].
    cbn [evalRuns]; rewrite <- hdec.
    rewrite !evalRuns_pushRunK, npow_1.
    unfold evalSym, D_word, bitSym. rewrite !Str_app_assoc. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sw01 (n + 1) hposDec) |].
    cbn [evalRuns]; rewrite <- hdec.
    rewrite !evalRuns_pushRunK.
    unfold evalSym, S_word, bitSym.
    replace (1 + n) with (n + 1) by lia.
    rewrite !Str_app_assoc. reflexivity.
  - destruct (N.eqb a 0) eqn:ha.
    + apply N.eqb_eq in ha; subst a.
      destruct (N.eqb c 0) eqn:hc.
      * apply N.eqb_eq in hc; subst c.
        split_and; [reflexivity | exact (AllPos_pushRunK Sw01 1 (AllPos_pushRunK (SS 0) 1 hposDec)) |].
        cbn [evalRuns]; rewrite <- hdec.
        rewrite !evalRuns_pushRunK, !npow_1.
        unfold evalSym, B_word, S_word, bitSym.
        rewrite !npow_0, !npow_1, !Str_app_assoc. reflexivity.
      * apply N.eqb_neq in hc.
        split_and; [reflexivity | exact (AllPos_pushRunK Sb1 (c - 1) (AllPos_pushRunK (SS 0) 2 hposDec)) |].
        cbn [evalRuns]; rewrite <- hdec.
        rewrite !evalRuns_pushRunK, npow_2.
        unfold evalSym, B_word, bitSym.
        replace c with (1 + (c - 1)) at 1 by lia.
        rewrite npow_0, npow_one_add, !Str_app_assoc. reflexivity.
    + apply N.eqb_neq in ha.
      split_and;
        [reflexivity | exact (AllPos_pushRunK Sb0 1 (AllPos_pushRunK Sw10 (a - 1)
          (AllPos_pushRunK Sb1 c (AllPos_pushRunK (SS 0) 2 hposDec)))) |].
      cbn [evalRuns]; rewrite <- hdec.
      rewrite !evalRuns_pushRunK, !npow_1, npow_2.
      unfold evalSym, B_word, bitSym.
      replace a with (1 + (a - 1)) at 1 by lia.
      rewrite npow_one_add, !Str_app_assoc. reflexivity.
  - split_and; [reflexivity | exact hposDec |].
    cbn [evalRuns]; rewrite <- hdec. reflexivity.
  - split_and; [reflexivity | exact hposDec |].
    cbn [evalRuns]; rewrite <- hdec. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sb0 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite evalRuns_pushRunK, npow_1. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sb1 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite evalRuns_pushRunK, npow_1. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sb0 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite evalRuns_pushRunK, npow_1. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sb1 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite evalRuns_pushRunK, npow_1. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sw11 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite evalRuns_pushRunK, npow_1. reflexivity.
  - split_and; [reflexivity | exact (AllPos_pushRunK Sb1 1 (AllPos_pushRunK Sw01 1 hposDec)) |].
    cbn [evalRuns]; rewrite <- hdec. rewrite !evalRuns_pushRunK, !npow_1. reflexivity.
Qed.

Lemma takeBitRunsK_spec_nonempty (b : bool) (r : Run) (rest xs' : Runs) (tail : side)
  (hpos : AllPos (r :: rest)) (h : takeBitRunsK b (r :: rest) = Some xs') :
  AllPos xs' /\ evalRuns (r :: rest) tail = bitSym b >> evalRuns xs' tail.
Proof.
  pose proof (popBitRunsK_spec r rest tail hpos) as hpop.
  destruct (popBitRunsK (r :: rest)) as [bp ys] eqn:hp.
  destruct hpop as [hbp [hpys he]].
  unfold takeBitRunsK in h.
  rewrite <- hbp, hp in h.
  destruct b, bp; simpl in h; try discriminate;
    inversion h; subst; exact (conj hpys he).
Qed.

Lemma takeBitRunsK_spec (b : bool) (xs xs' : Runs) (hpos : AllPos xs)
  (h : takeBitRunsK b xs = Some xs') :
  AllPos xs' /\ evalRuns xs 0inf = bitSym b >> evalRuns xs' 0inf.
Proof.
  destruct xs as [| r rest].
  - destruct b; simpl in h; [discriminate |].
    inversion h; subst. split; [exact I |].
    simpl. symmetry; exact zero_cons_default.
  - exact (takeBitRunsK_spec_nonempty b r rest xs' 0inf hpos h).
Qed.

Lemma takeBits2RunsK_spec (b0 b1 : bool) (xs xs' : Runs) (hpos : AllPos xs)
  (h : takeBits2RunsK b0 b1 xs = Some xs') :
  AllPos xs' /\ evalRuns xs 0inf = bitSym b0 >> (bitSym b1 >> evalRuns xs' 0inf).
Proof.
  unfold takeBits2RunsK in h.
  destruct (takeBitRunsK b0 xs) as [xs1 |] eqn:h1; [| discriminate].
  destruct (takeBitRunsK_spec b0 xs xs1 hpos h1) as [hp1 he1].
  destruct (takeBitRunsK_spec b1 xs1 xs' hp1 h) as [hp2 he2].
  split; [exact hp2 | rewrite he1, he2; reflexivity].
Qed.

Lemma takeBits5RunsK_spec (b0 b1 b2 b3 b4 : bool) (xs xs' : Runs) (hpos : AllPos xs)
  (h : takeBits5RunsK b0 b1 b2 b3 b4 xs = Some xs') :
  AllPos xs' /\
  evalRuns xs 0inf =
    [bitSym b0; bitSym b1; bitSym b2; bitSym b3; bitSym b4] *> evalRuns xs' 0inf.
Proof.
  unfold takeBits5RunsK in h.
  destruct (takeBitRunsK b0 xs) as [x1 |] eqn:h1; [| discriminate].
  destruct (takeBitRunsK b1 x1) as [x2 |] eqn:h2; [| discriminate].
  destruct (takeBitRunsK b2 x2) as [x3 |] eqn:h3; [| discriminate].
  destruct (takeBitRunsK b3 x3) as [x4 |] eqn:h4; [| discriminate].
  destruct (takeBitRunsK_spec b0 xs x1 hpos h1) as [p1 e1].
  destruct (takeBitRunsK_spec b1 x1 x2 p1 h2) as [p2 e2].
  destruct (takeBitRunsK_spec b2 x2 x3 p2 h3) as [p3 e3].
  destruct (takeBitRunsK_spec b3 x3 x4 p3 h4) as [p4 e4].
  destruct (takeBitRunsK_spec b4 x4 xs' p4 h) as [p5 e5].
  split; [exact p5 | rewrite e1, e2, e3, e4, e5; reflexivity].
Qed.

Lemma takeBitRK_spec (b : bool) (Rh Rt Rh' Rt' : Runs) (d0 d' : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : takeBitRK b Rh Rt d0 = Some (Rh', Rt', d')) :
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  evalR Rh Rt d0 = bitSym b >> evalR Rh' Rt' d'.
Proof.
  unfold takeBitRK in h.
  destruct Rh as [| r rest].
  - destruct Rt as [| [w k] rrest].
    + destruct (N.eqb d0 0) eqn:hd0.
      * destruct b; [discriminate |].
        inversion h; subst. apply N.eqb_eq in hd0; subst d0.
        split_and; try exact I.
        unfold evalR; simpl. rewrite ?npow_0; simpl.
        symmetry; exact zero_cons_default.
      * destruct b; [| discriminate].
        inversion h; subst. apply N.eqb_neq in hd0.
        split_and; try exact I; [simpl; split; [lia | exact I] |].
        cbn [evalR evalRuns evalSym].
        replace d0 with (1 + (d0 - 1)) at 1 by lia.
        rewrite npow_one_add, npow_1, Str_app_assoc.
        unfold D_word; rewrite npow_0; simpl. reflexivity.
    + destruct w; try contradiction.
      destruct b; [| discriminate].
      inversion h; subst.
      pose proof (evalRuns_decRunK (SD n) k rrest (npow (D_word 0) d' *> 0inf) (proj1 hRt)) as hdec.
      split_and.
      * apply AllPos_pushRunK; simpl; split; [lia | exact I].
      * exact (AllPos_decRunK (SD n) k (proj2 hRt)).
      * exact (AllD_decRunK n k hD).
      * unfold evalR; cbn [evalRuns]. rewrite <- hdec.
        rewrite evalRuns_pushRunK; cbn [evalRuns]. rewrite npow_1.
        unfold evalSym, D_word, bitSym. rewrite !Str_app_assoc. reflexivity.
  - destruct (takeBitRunsK b (r :: rest)) as [Rh1 |] eqn:ht; [| discriminate].
    inversion h; subst.
    destruct (takeBitRunsK_spec_nonempty b r rest Rh' (evalRuns Rt' (npow (D_word 0) d' *> 0inf)) hRh ht)
      as [hp he].
    exact (conj hp (conj hRt (conj hD he))).
Qed.

Lemma takeBits2RK_spec (b0 b1 : bool) (Rh Rt Rh' Rt' : Runs) (d0 d' : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : takeBits2RK b0 b1 Rh Rt d0 = Some (Rh', Rt', d')) :
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  evalR Rh Rt d0 = bitSym b0 >> (bitSym b1 >> evalR Rh' Rt' d').
Proof.
  unfold takeBits2RK in h.
  destruct (takeBitRK b0 Rh Rt d0) as [[[Rh1 Rt1] d1] |] eqn:h1; [| discriminate].
  destruct (takeBitRK b1 Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:h2; [| discriminate].
  destruct (takeBitRK_spec b0 Rh Rt Rh1 Rt1 d0 d1 hRh hRt hD h1) as [p1 [q1 [d1h e1]]].
  destruct (takeBitRK_spec b1 Rh1 Rt1 Rh2 Rt2 d1 d2 p1 q1 d1h h2) as [p2 [q2 [d2h e2]]].
  pose proof (normRK_spec Rh2 Rt2 d2 p2 q2 d2h) as hn.
  destruct (normRK Rh2 Rt2) as [Rh3 Rt3].
  inversion h; subst.
  destruct hn as [p3 [q3 [d3h e3]]].
  split_and; [exact p3 | exact q3 | exact d3h | rewrite e1, e2, <- e3; reflexivity].
Qed.

Lemma takeBits3RK_spec (b0 b1 b2 : bool) (Rh Rt Rh' Rt' : Runs) (d0 d' : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : takeBits3RK b0 b1 b2 Rh Rt d0 = Some (Rh', Rt', d')) :
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  evalR Rh Rt d0 = [bitSym b0; bitSym b1; bitSym b2] *> evalR Rh' Rt' d'.
Proof.
  unfold takeBits3RK in h.
  destruct (takeBitRK b0 Rh Rt d0) as [[[Rh1 Rt1] d1] |] eqn:h1; [| discriminate].
  destruct (takeBitRK b1 Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:h2; [| discriminate].
  destruct (takeBitRK b2 Rh2 Rt2 d2) as [[[Rh3 Rt3] d3] |] eqn:h3; [| discriminate].
  destruct (takeBitRK_spec b0 Rh Rt Rh1 Rt1 d0 d1 hRh hRt hD h1) as [p1 [q1 [d1h e1]]].
  destruct (takeBitRK_spec b1 Rh1 Rt1 Rh2 Rt2 d1 d2 p1 q1 d1h h2) as [p2 [q2 [d2h e2]]].
  destruct (takeBitRK_spec b2 Rh2 Rt2 Rh3 Rt3 d2 d3 p2 q2 d2h h3) as [p3 [q3 [d3h e3]]].
  pose proof (normRK_spec Rh3 Rt3 d3 p3 q3 d3h) as hn.
  destruct (normRK Rh3 Rt3) as [Rh4 Rt4].
  inversion h; subst.
  destruct hn as [p4 [q4 [d4h e4]]].
  split_and; [exact p4 | exact q4 | exact d4h | rewrite e1, e2, e3, <- e4; reflexivity].
Qed.

Lemma takeOnesRunsAux_spec (xs : Runs) (acc : N) (tail : side) (hpos : AllPos xs) :
  let '(c, xs') := takeOnesRunsAux xs acc in
  AllPos xs' /\ npow [S1] acc *> evalRuns xs tail = npow [S1] c *> evalRuns xs' tail.
Proof.
  revert acc.
  induction xs as [| [w k] rest ih]; intro acc; [exact (conj I eq_refl) |].
  destruct hpos as [hk hrest].
  assert (hk0 : N.eqb k 0 = false) by (apply N.eqb_neq; lia).
  pose proof (evalRuns_decRunK w k rest tail hk) as hdec.
  pose proof (AllPos_decRunK w k hrest) as hposDec.
  cbn [takeOnesRunsAux]; rewrite hk0.
  destruct w as [n | n | a c | | | | | | | |].
  - split; [exact (AllPos_pushRunK Sw00 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec, evalRuns_pushRunK, npow_1.
    unfold evalSym, D_word.
    rewrite pow_11_eq_pow_1.
    replace (acc + (2 * n + 1)) with (acc + (1 + n * 2)) by lia.
    rewrite !npow_add, npow_1, !Str_app_assoc. reflexivity.
  - split; [exact (AllPos_pushRunK Sw01 (n + 1) hposDec) |].
    cbn [evalRuns]; rewrite <- hdec, evalRuns_pushRunK.
    unfold evalSym, S_word.
    replace (1 + n) with (n + 1) by lia.
    rewrite <- (npow_succ_right [S1] acc), !Str_app_assoc. reflexivity.
  - destruct (N.eqb a 0) eqn:ha.
    + apply N.eqb_eq in ha; subst a.
      split; [exact (AllPos_pushRunK Sw01 1 (AllPos_pushRunK (SS 0) 1 hposDec)) |].
      cbn [evalRuns]; rewrite <- hdec, !evalRuns_pushRunK, !npow_1.
      unfold evalSym, B_word, S_word.
      rewrite npow_0, npow_1, (npow_add [S1] acc (c + 1)), <- (npow_succ_right [S1] c), !Str_app_assoc. reflexivity.
    + apply N.eqb_neq in ha.
      split;
        [exact (AllPos_pushRunK Sb0 1 (AllPos_pushRunK Sw10 (a - 1)
          (AllPos_pushRunK Sb1 c (AllPos_pushRunK (SS 0) 2 hposDec)))) |].
      cbn [evalRuns]; rewrite <- hdec, !evalRuns_pushRunK, !npow_1, npow_2.
      unfold evalSym, B_word.
      replace a with (1 + (a - 1)) at 1 by lia.
      rewrite npow_one_add, <- (npow_succ_right [S1] acc), !Str_app_assoc. reflexivity.
  - exact (conj (conj hk hrest) eq_refl).
  - pose proof (ih hrest (acc + k)) as hrec.
    destruct (takeOnesRunsAux rest (acc + k)) as [c1 xs1].
    destruct hrec as [hp he]; split; [exact hp |].
    cbn [evalRuns]; unfold evalSym. rewrite npow_append_npow. exact he.
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - split; [exact (AllPos_pushRunK Sb0 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec, evalRuns_pushRunK, npow_1.
    unfold evalSym. rewrite <- (npow_succ_right [S1] acc), !Str_app_assoc. reflexivity.
  - pose proof (ih hrest (acc + 2 * k)) as hrec.
    destruct (takeOnesRunsAux rest (acc + 2 * k)) as [c1 xs1].
    destruct hrec as [hp he]; split; [exact hp |].
    cbn [evalRuns]; unfold evalSym.
    rewrite pow_11_eq_pow_1, npow_append_npow.
    replace (acc + k * 2) with (acc + 2 * k) by lia. exact he.
  - pose proof (ih hrest (acc + 3 * k)) as hrec.
    destruct (takeOnesRunsAux rest (acc + 3 * k)) as [c1 xs1].
    destruct hrec as [hp he]; split; [exact hp |].
    cbn [evalRuns]; unfold evalSym.
    rewrite pow_111_eq_pow_1, npow_append_npow.
    replace (acc + k * 3) with (acc + 3 * k) by lia. exact he.
  - split; [exact (AllPos_pushRunK Sw01 1 hposDec) |].
    cbn [evalRuns]; rewrite <- hdec, evalRuns_pushRunK, npow_1.
    unfold evalSym. rewrite npow_add, npow_2, !Str_app_assoc. reflexivity.
Qed.

Lemma takeOnesRunsK_spec (xs : Runs) (tail : side) (hpos : AllPos xs) :
  let '(c, xs') := takeOnesRunsK xs in
  AllPos xs' /\ evalRuns xs tail = npow [S1] c *> evalRuns xs' tail.
Proof.
  unfold takeOnesRunsK.
  pose proof (takeOnesRunsAux_spec xs 0 tail hpos) as h.
  rewrite npow_0 in h. exact h.
Qed.

Lemma takeOnesRK_spec (Rh Rt : Runs) (d0 : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt) :
  let '(c, Rh', Rt', d') := takeOnesRK Rh Rt d0 in
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  evalR Rh Rt d0 = npow [S1] c *> evalR Rh' Rt' d'.
Proof.
  unfold takeOnesRK.
  pose proof (takeOnesRunsK_spec Rh (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) hRh) as h1.
  destruct (takeOnesRunsK Rh) as [c0 Rh1].
  destruct h1 as [hpRh1 heRh1].
  destruct Rh1 as [| r1 rest1]; [| exact (conj hpRh1 (conj hRt (conj hD heRh1)))].
  destruct Rt as [| [w k] rest].
  - destruct (N.eqb d0 0) eqn:hd0.
    + apply N.eqb_eq in hd0; subst d0.
      exact (conj I (conj I (conj I heRh1))).
    + apply N.eqb_neq in hd0.
      split_and; try exact I; [simpl; split; [lia | exact I] |].
      unfold evalR in *; rewrite heRh1; cbn [evalRuns evalSym].
      rewrite npow_1.
      replace d0 with (1 + (d0 - 1)) at 1 by lia.
      rewrite npow_one_add, <- (npow_succ_right [S1] c0).
      unfold D_word; rewrite npow_0, !Str_app_assoc. reflexivity.
  - destruct w; try contradiction.
    pose proof (evalRuns_decRunK (SD n) k rest (npow (D_word 0) d0 *> 0inf) (proj1 hRt)) as hdec.
    split_and.
    + simpl; split; [lia | exact I].
    + exact (AllPos_decRunK (SD n) k (proj2 hRt)).
    + exact (AllD_decRunK n k hD).
    + unfold evalR in *; rewrite heRh1; cbn [evalRuns]; rewrite <- hdec.
      rewrite npow_1.
      unfold evalSym, D_word.
      rewrite pow_11_eq_pow_1.
      replace (c0 + (2 * n + 1)) with (c0 + (1 + n * 2)) by lia.
      rewrite !npow_add, npow_1, !Str_app_assoc. reflexivity.
Qed.

Lemma take10RunsAux_spec (fuel : nat) (acc : N) (cur : Runs) (tail : side) (hcur : AllPos cur) :
  let '(c, xs') := take10RunsAux fuel acc cur in
  AllPos xs' /\ npow [S1; S0] acc *> evalRuns cur tail = npow [S1; S0] c *> evalRuns xs' tail.
Proof.
  revert acc cur hcur.
  induction fuel as [| fuel' ih]; intros acc cur hcur; [exact (conj hcur eq_refl) |].
  destruct cur as [| [w k] rest]; [exact (conj I eq_refl) |].
  destruct hcur as [hk hrest].
  assert (hk0 : N.eqb k 0 = false) by (apply N.eqb_neq; lia).
  cbn [take10RunsAux]; rewrite hk0.
  destruct w.
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - destruct (N.eqb k 1) eqn:hk1; [| exact (conj (conj hk hrest) eq_refl)].
    apply N.eqb_eq in hk1; subst k.
    destruct rest as [| [nw nk] rest2]; [exact (conj (conj hk I) eq_refl) |].
    pose proof (popBitRunsK_spec (mkRun nw nk) rest2 tail hrest) as hpop.
    destruct (popBitRunsK (mkRun nw nk :: rest2)) as [bp rest'] eqn:hpr.
    destruct hpop as [hbp [hpr' hpe]].
    destruct nw; try exact (conj (conj hk hrest) eq_refl);
      simpl in hbp; subst bp;
      pose proof (ih (acc + 1) rest' hpr') as hrec;
      destruct (take10RunsAux fuel' (acc + 1) rest') as [c1 xs1];
      destruct hrec as [hp he]; (split; [exact hp |]);
      rewrite (fun xs : Runs => (eq_refl : evalRuns (mkRun Sb1 1 :: xs) tail = npow [S1] 1 *> evalRuns xs tail));
      rewrite npow_1, hpe, <- he, <- (npow_succ_right [S1; S0] acc), !Str_app_assoc; reflexivity.
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - pose proof (ih (acc + k) rest hrest) as hrec.
    destruct (take10RunsAux fuel' (acc + k) rest) as [c1 xs1].
    destruct hrec as [hp he]; split; [exact hp |].
    cbn [evalRuns]; unfold evalSym. rewrite npow_append_npow. exact he.
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
  - exact (conj (conj hk hrest) eq_refl).
Qed.

Lemma take10RunsK_spec (f64 : nat) (xs : Runs) (tail : side) (hpos : AllPos xs) :
  let '(c, xs') := take10RunsK f64 xs in
  AllPos xs' /\ evalRuns xs tail = npow [S1; S0] c *> evalRuns xs' tail.
Proof.
  unfold take10RunsK.
  pose proof (take10RunsAux_spec f64 0 xs tail hpos) as h.
  rewrite npow_0 in h. exact h.
Qed.

Lemma take01RunsAux_spec (fuel : nat) (acc : N) (cur : Runs) (hcur : AllPos cur) :
  let '(c, xs') := take01RunsAux fuel acc cur in
  AllPos xs' /\ npow [S0; S1] acc *> evalRuns cur 0inf = npow [S0; S1] c *> evalRuns xs' 0inf.
Proof.
  revert acc cur hcur.
  induction fuel as [| fuel' ih]; intros acc cur hcur; [exact (conj hcur eq_refl) |].
  destruct cur as [| [w k] rest]; [exact (conj I eq_refl) |].
  destruct hcur as [hk hrest].
  assert (hk0 : N.eqb k 0 = false) by (apply N.eqb_neq; lia).
  cbn [take01RunsAux]; rewrite hk0.
  assert (h2 :
    let '(c, xs') :=
      match takeBits2RunsK false true (mkRun w k :: rest) with
      | Some cur' => take01RunsAux fuel' (acc + 1) cur'
      | None => (acc, mkRun w k :: rest)
      end in
    AllPos xs' /\ npow [S0; S1] acc *> evalRuns (mkRun w k :: rest) 0inf = npow [S0; S1] c *> evalRuns xs' 0inf).
  { destruct (takeBits2RunsK false true (mkRun w k :: rest)) as [cur' |] eqn:ht;
      [| exact (conj (conj hk hrest) eq_refl)].
    destruct (takeBits2RunsK_spec false true (mkRun w k :: rest) cur' (conj hk hrest) ht) as [hp1 he1].
    pose proof (ih (acc + 1) cur' hp1) as hrec.
    destruct (take01RunsAux fuel' (acc + 1) cur') as [c1 xs1].
    destruct hrec as [hp2 he2]; split; [exact hp2 |].
    rewrite he1, <- he2, <- (npow_succ_right [S0; S1] acc), !Str_app_assoc. reflexivity. }
  destruct w; try exact h2.
  pose proof (ih (acc + k) rest hrest) as hrec.
  destruct (take01RunsAux fuel' (acc + k) rest) as [c1 xs1].
  destruct hrec as [hp he]; split; [exact hp |].
  simpl evalRuns; unfold evalSym. rewrite npow_append_npow. exact he.
Qed.

Lemma take01RunsK_spec (f64 : nat) (xs : Runs) (hpos : AllPos xs) :
  let '(c, xs') := take01RunsK f64 xs in
  AllPos xs' /\ evalRuns xs 0inf = npow [S0; S1] c *> evalRuns xs' 0inf.
Proof.
  unfold take01RunsK.
  pose proof (take01RunsAux_spec f64 0 xs hpos) as h.
  rewrite npow_0 in h. exact h.
Qed.

Lemma take111Prefix_spec (xs : Runs) (acc : N) (tail : side) (hpos : AllPos xs) :
  let '(c0, xs1) := take111Prefix xs acc in
  AllPos xs1 /\ npow [S1; S1; S1] acc *> evalRuns xs tail = npow [S1; S1; S1] c0 *> evalRuns xs1 tail.
Proof.
  revert acc.
  induction xs as [| [w k] rest ih]; intro acc; [exact (conj I eq_refl) |].
  destruct w; try exact (conj hpos eq_refl).
  cbn [take111Prefix].
  pose proof (ih (proj2 hpos) (acc + k)) as hrec.
  destruct (take111Prefix rest (acc + k)) as [c0 xs1].
  destruct hrec as [hp he]; split; [exact hp |].
  simpl evalRuns; unfold evalSym. rewrite npow_append_npow. exact he.
Qed.

Lemma take111RunsK_spec (xs : Runs) (tail : side) (hpos : AllPos xs) :
  let '(c, xs') := take111RunsK xs in
  AllPos xs' /\ evalRuns xs tail = npow [S1; S1; S1] c *> evalRuns xs' tail.
Proof.
  unfold take111RunsK.
  pose proof (take111Prefix_spec xs 0 tail hpos) as hpre.
  rewrite npow_0 in hpre; simpl Str_app in hpre.
  destruct (take111Prefix xs 0) as [c0 xs1].
  destruct hpre as [hpos1 he1].
  destruct xs1 as [| [w k] rest]; [exact (conj I he1) |].
  assert (hgo :
    let '(c, xs') :=
      let '(ones, xs2) := takeOnesRunsK (mkRun w k :: rest) in
      if N.eqb (ones mod 3) 0 then (c0 + ones / 3, xs2)
      else if N.eqb (ones mod 3) 1 then (c0 + ones / 3, pushRunK Sb1 1 xs2)
      else (c0 + ones / 3, pushRunK Sw11 1 xs2) in
    AllPos xs' /\ evalRuns xs tail = npow [S1; S1; S1] c *> evalRuns xs' tail).
  { pose proof (takeOnesRunsK_spec (mkRun w k :: rest) tail hpos1) as hto.
    destruct (takeOnesRunsK (mkRun w k :: rest)) as [ones xs2].
    destruct hto as [hp2 he2].
    destruct (N.eqb (ones mod 3) 0) eqn:hr0.
    - apply N.eqb_eq in hr0. split; [exact hp2 |].
      rewrite he1, he2.
      replace ones with ((ones / 3) * 3) at 1 by lia.
      rewrite <- pow_111_eq_pow_1, npow_append_npow. reflexivity.
    - apply N.eqb_neq in hr0.
      destruct (N.eqb (ones mod 3) 1) eqn:hr1.
      + apply N.eqb_eq in hr1. split; [exact (AllPos_pushRunK Sb1 1 hp2) |].
        rewrite he1, he2, evalRuns_pushRunK, npow_1.
        replace ones with ((ones / 3) * 3 + 1) at 1 by lia.
        rewrite npow_add, npow_1, <- pow_111_eq_pow_1, !Str_app_assoc, npow_append_npow.
        reflexivity.
      + apply N.eqb_neq in hr1. split; [exact (AllPos_pushRunK Sw11 1 hp2) |].
        rewrite he1, he2, evalRuns_pushRunK, npow_1.
        replace ones with ((ones / 3) * 3 + 2) at 1 by lia.
        rewrite npow_add, npow_2, <- pow_111_eq_pow_1, !Str_app_assoc, npow_append_npow.
        reflexivity. }
  destruct w; try exact hgo; exact (conj hpos1 he1).
Qed.

Lemma tryTakeDRK_spec (Rh Rt Rh' Rt' : Runs) (d0 dn d' : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : tryTakeDRK Rh Rt d0 = Some (dn, Rh', Rt', d')) :
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\ evalR Rh Rt d0 = D_word dn *> evalR Rh' Rt' d'.
Proof.
  unfold tryTakeDRK in h.
  destruct Rh as [| [w k] rest].
  - destruct Rt as [| [wt kt] rrest].
    + destruct (N.eqb d0 0) eqn:hd0; [discriminate |].
      inversion h; subst. apply N.eqb_neq in hd0.
      split_and; try exact I.
      unfold evalR; simpl.
      replace d0 with (1 + (d0 - 1)) at 1 by lia.
      rewrite npow_one_add, Str_app_assoc. reflexivity.
    + destruct wt; try contradiction.
      inversion h; subst.
      pose proof (evalRuns_decRunK (SD dn) kt rrest (npow (D_word 0) d' *> 0inf) (proj1 hRt)) as hdec.
      split_and; [exact I | exact (AllPos_decRunK (SD dn) kt (proj2 hRt)) | exact (AllD_decRunK dn kt hD) |].
      unfold evalR; simpl. symmetry; exact hdec.
  - assert (hodd :
      (let '(c1, Rh1, Rt1, d1) := takeOnesRK (mkRun w k :: rest) Rt d0 in
       if N.eqb (N.b2n (N.odd c1)) 1 then
         match takeBits2RK false false Rh1 Rt1 d1 with
         | Some (Rh2, Rt2, d2) => Some (N.div2 c1, Rh2, Rt2, d2)
         | None => None
         end
       else None) = Some (dn, Rh', Rt', d') ->
      AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
      evalR (mkRun w k :: rest) Rt d0 = D_word dn *> evalR Rh' Rt' d').
    { intro ho.
      pose proof (takeOnesRK_spec (mkRun w k :: rest) Rt d0 hRh hRt hD) as hto.
      destruct (takeOnesRK (mkRun w k :: rest) Rt d0) as [[[c1 Rh1] Rt1] d1].
      destruct hto as [p1 [q1 [d1h e1]]].
      rewrite N_b2n_odd_mod2 in ho.
      destruct (N.eqb (c1 mod 2) 1) eqn:hm; [| discriminate].
      apply N.eqb_eq in hm.
      destruct (takeBits2RK false false Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:h2; [| discriminate].
      inversion ho; subst.
      destruct (takeBits2RK_spec false false Rh1 Rt1 Rh' Rt' d1 d' p1 q1 d1h h2) as [p2 [q2 [d2h e2]]].
      split_and; [exact p2 | exact q2 | exact d2h |].
      rewrite e1, e2, N.div2_div.
      replace c1 with (1 + (c1 / 2) * 2) at 1 by lia.
      rewrite npow_one_add, <- pow_11_eq_pow_1.
      unfold D_word, bitSym; rewrite !Str_app_assoc. reflexivity. }
    destruct w; try (exact (hodd h)); try discriminate.
    pose proof (evalRuns_decRunK (SD n) k rest (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) (proj1 hRh)) as hdec.
    pose proof (normRK_spec (decRunK (SD n) k rest) Rt d0 (AllPos_decRunK (SD n) k (proj2 hRh)) hRt hD) as hn.
    destruct (normRK (decRunK (SD n) k rest) Rt) as [Rh1 Rt1].
    inversion h; subst.
    destruct hn as [p1 [q1 [d1h e1]]].
    split_and; [exact p1 | exact q1 | exact d1h |].
    unfold evalR in *; cbn [evalRuns].
    rewrite <- hdec, <- e1. reflexivity.
Qed.

Lemma tryTakeSK_spec (f64 : nat) (L L' : Runs) (sn : N) (hpos : AllPos L)
  (h : tryTakeSK f64 L = Some (sn, L')) :
  AllPos L' /\ evalRuns L 0inf = S_word sn *> evalRuns L' 0inf.
Proof.
  unfold tryTakeSK in h.
  destruct L as [| [w k] rest]; [discriminate |].
  assert (hgen :
    match takeBitRunsK true (mkRun w k :: rest) with
    | Some L1 =>
      let '(c01, L2) := take01RunsK f64 L1 in
      if N.eqb c01 0 then None else Some (c01 - 1, L2)
    | None => None
    end = Some (sn, L') ->
    AllPos L' /\ evalRuns (mkRun w k :: rest) 0inf = S_word sn *> evalRuns L' 0inf).
  { intro hg.
    destruct (takeBitRunsK true (mkRun w k :: rest)) as [L1 |] eqn:ht; [| discriminate].
    destruct (takeBitRunsK_spec true (mkRun w k :: rest) L1 hpos ht) as [hp1 he1].
    pose proof (take01RunsK_spec f64 L1 hp1) as h01.
    destruct (take01RunsK f64 L1) as [c01 L2].
    destruct h01 as [hp2 he2].
    destruct (N.eqb c01 0) eqn:hc0; [discriminate |].
    apply N.eqb_neq in hc0. inversion hg; subst.
    split; [exact hp2 |].
    rewrite he1, he2. unfold S_word, bitSym.
    replace (1 + (c01 - 1)) with c01 by lia.
    rewrite !Str_app_assoc. reflexivity. }
  destruct w; try (exact (hgen h)); try discriminate.
  - inversion h; subst.
    split; [exact (AllPos_decRunK (SS sn) k (proj2 hpos)) |].
    symmetry; exact (evalRuns_decRunK (SS sn) k rest 0inf (proj1 hpos)).
  - destruct (takeBitRunsK true rest) as [rest' |] eqn:ht.
    + inversion h; subst.
      destruct (takeBitRunsK_spec true rest L' (proj2 hpos) ht) as [hp' he'].
      split; [exact hp' |].
      cbn [evalRuns]; rewrite he'. unfold evalSym, bitSym.
      pose proof (proj1 hpos) as hk.
      replace k with (1 + (k - 1)) at 1 by lia.
      exact (w10_pow_one_eq_S (k - 1) (evalRuns L' 0inf)).
    + destruct (N.leb k 1) eqn:hle; [discriminate |].
      apply N.leb_gt in hle. inversion h; subst.
      split; [exact (AllPos_pushRunK Sb0 1 (proj2 hpos)) |].
      cbn [evalRuns]; rewrite evalRuns_pushRunK, npow_1.
      unfold evalSym.
      replace k with ((1 + (k - 2)) + 1) at 1 by lia.
      rewrite <- npow_succ_right, !Str_app_assoc.
      exact (w10_pow_one_eq_S (k - 2) (S0 >> evalRuns rest 0inf)).
Qed.

Lemma splitDPrefixAux_spec (Rh acc : Runs) (tail : side)
  (hRh : AllPos Rh) (haccP : AllPos acc) (haccD : AllD acc) :
  let '(dpref, rtail) := splitDPrefixAux Rh acc in
  AllPos dpref /\ AllD dpref /\ AllPos rtail /\
  evalRuns (rev acc) (evalRuns Rh tail) = evalRuns (rev dpref) (evalRuns rtail tail).
Proof.
  revert acc haccP haccD.
  induction Rh as [| [w k] rest ih]; intros acc haccP haccD;
    [exact (conj haccP (conj haccD (conj I eq_refl))) |].
  destruct w; try exact (conj haccP (conj haccD (conj hRh eq_refl))).
  cbn [splitDPrefixAux].
  pose proof (ih (proj2 hRh) (mkRun (SD n) k :: acc) (conj (proj1 hRh) haccP) haccD) as hrec.
  destruct (splitDPrefixAux rest (mkRun (SD n) k :: acc)) as [dpref rtail].
  destruct hrec as [p1 [d1 [p2 e1]]].
  split_and; [exact p1 | exact d1 | exact p2 |].
  simpl rev in e1; rewrite evalRuns_append in e1; simpl evalRuns in e1.
  exact e1.
Qed.

Lemma splitDPrefixK_spec (Rh : Runs) (tail : side) (hRh : AllPos Rh) :
  let '(dpref, rtail) := splitDPrefixK Rh in
  AllPos dpref /\ AllD dpref /\ AllPos rtail /\
  evalRuns Rh tail = evalRuns (rev dpref) (evalRuns rtail tail).
Proof.
  unfold splitDPrefixK.
  exact (splitDPrefixAux_spec Rh [] tail hRh I I).
Qed.

Lemma restoreDPrefK_spec (dpref Rh Rt : Runs) (d0 : N)
  (hdpP : AllPos dpref) (hdpD : AllD dpref) (hRh : AllPos Rh) (hRt : AllPos Rt) (hDRt : AllD Rt) :
  let '(nRh, nRt) := restoreDPrefK dpref Rh Rt in
  AllPos nRh /\ AllPos nRt /\ AllD nRt /\
  evalR nRh nRt d0 = evalRuns (rev dpref) (evalR Rh Rt d0).
Proof.
  revert Rh Rt hRh hRt hDRt.
  induction dpref as [| [w k] rest ih]; intros Rh Rt hRh hRt hDRt;
    [exact (conj hRh (conj hRt (conj hDRt eq_refl))) |].
  simpl in hdpD; destruct w; try contradiction.
  cbn [restoreDPrefK].
  pose proof (pushRDK_spec n k Rh Rt d0 hRh hRt hDRt) as hp.
  destruct (pushRDK n k Rh Rt) as [Rh1 Rt1].
  destruct hp as [p1 [q1 [d1 e1]]].
  pose proof (ih (proj2 hdpP) hdpD Rh1 Rt1 p1 q1 d1) as hrec.
  destruct (restoreDPrefK rest Rh1 Rt1) as [nRh nRt].
  destruct hrec as [p2 [q2 [d2 e2]]].
  split_and; [exact p2 | exact q2 | exact d2 |].
  rewrite e2, e1; simpl rev; rewrite evalRuns_append; simpl evalRuns. reflexivity.
Qed.

Lemma OneCall_prepend_allD (xs : Runs) (hD : AllD xs) {r r' : side} (h : OneCall r r') :
  OneCall (evalRuns xs r) (evalRuns xs r').
Proof.
  induction xs as [| [w k] rest ih]; simpl in *; [exact h |].
  destruct w; try contradiction.
  exact (OneCall_prepend_D_pow n k (ih hD)).
Qed.

Lemma NCalls_prepend_allD (xs : Runs) (hD : AllD xs) {n : N} {r r' : side}
  (h : NCalls n r r') : NCalls n (evalRuns xs r) (evalRuns xs r').
Proof.
  unfold NCalls in *.
  induction h as [r0 | k r1 r2 r3 h1 _ ih].
  - constructor.
  - exact (NCallsNat_succ (OneCall_prepend_allD xs hD h1) ih).
Qed.

Lemma NCalls_pureD_tail (Rt : Runs) (hD : AllD Rt) (n d0 : N) :
  NCalls n (evalR [] Rt d0) (evalR [] Rt (d0 + 2 * n)).
Proof.
  unfold evalR; simpl evalRuns.
  exact (NCalls_prepend_allD Rt hD (NCalls_D0_pow n d0)).
Qed.

Lemma peekHeadD3K_spec (Rh Rt : Runs) (d0 a0 k0 d1 : N) (rH1 rT1 : Runs)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : peekHeadD3K Rh Rt d0 = Some (a0, k0, rH1, rT1, d1)) :
  1 <= k0 /\ AllPos rH1 /\ AllPos rT1 /\ AllD rT1 /\
  evalR Rh Rt d0 = npow (D_word a0) k0 *> evalR rH1 rT1 d1.
Proof.
  unfold peekHeadD3K in h.
  destruct Rh as [| [w k] rest].
  - destruct Rt as [| [wt kt] rrest].
    + destruct (N.eqb d0 0) eqn:hd0; [discriminate |].
      apply N.eqb_neq in hd0. inversion h; subst.
      split_and; try exact I; [lia |].
      unfold evalR; simpl; rewrite ?npow_0; reflexivity.
    + destruct wt; try contradiction.
      destruct rrest as [| r2 rest2].
      * destruct (N.eqb n 0) eqn:hn.
        -- apply N.eqb_eq in hn; subst n. inversion h; subst.
           pose proof (proj1 hRt) as hkt.
           split_and; try exact I; [lia |].
           unfold evalR; simpl. rewrite ?npow_0, npow_append_npow. reflexivity.
        -- inversion h; subst.
           split_and; try exact I; [exact (proj1 hRt) | reflexivity].
      * inversion h; subst.
        split_and; [exact (proj1 hRt) | exact I | exact (proj2 hRt) | exact hD | reflexivity].
  - destruct w; try discriminate.
    destruct rest as [| r2 rest2].
    + destruct Rt as [| rt0 rtRest].
      * destruct (N.eqb n 0) eqn:hn.
        -- apply N.eqb_eq in hn; subst n. inversion h; subst.
           pose proof (proj1 hRh) as hk.
           split_and; try exact I; [lia |].
           unfold evalR; simpl. rewrite ?npow_0, npow_append_npow. reflexivity.
        -- inversion h; subst.
           split_and; try exact I; [exact (proj1 hRh) | reflexivity].
      * inversion h; subst.
        split_and; [exact (proj1 hRh) | exact I | exact hRt | exact hD | reflexivity].
    + inversion h; subst.
      split_and; [exact (proj1 hRh) | exact (proj2 hRh) | exact hRt | exact hD | reflexivity].
Qed.

Lemma popOneD3K_spec (Rh Rt Rh' Rt' : Runs) (d0 d d' : N)
  (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : popOneD3K Rh Rt d0 = Some (d, Rh', Rt', d')) :
  AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\ evalR Rh Rt d0 = D_word d *> evalR Rh' Rt' d'.
Proof.
  unfold popOneD3K in h.
  destruct Rh as [| [w k] rest].
  - destruct Rt as [| [wt kt] rrest].
    + destruct (N.eqb d0 0) eqn:hd0; [discriminate |].
      apply N.eqb_neq in hd0. inversion h; subst.
      split_and; try exact I.
      unfold evalR; simpl.
      replace d0 with (1 + (d0 - 1)) at 1 by lia.
      rewrite npow_one_add, Str_app_assoc. reflexivity.
    + destruct wt; try contradiction.
      inversion h; subst.
      pose proof (evalRuns_decRunK (SD d) kt rrest (npow (D_word 0) d' *> 0inf) (proj1 hRt)) as hdec.
      split_and; [exact I | exact (AllPos_decRunK (SD d) kt (proj2 hRt)) | exact (AllD_decRunK d kt hD) |].
      unfold evalR; simpl. symmetry; exact hdec.
  - destruct w; try discriminate.
    inversion h; subst.
    pose proof (evalRuns_decRunK (SD d) k rest (evalRuns Rt' (npow (D_word 0) d' *> 0inf)) (proj1 hRh)) as hdec.
    split_and; [exact (AllPos_decRunK (SD d) k (proj2 hRh)) | exact hRt | exact hD |].
    unfold evalR; simpl. symmetry; exact hdec.
Qed.

Lemma putBackD3K_spec (a0 rem : N) (rH1 rT1 : Runs) (d1 : N)
  (hrH1P : AllPos rH1) (hrT1P : AllPos rT1) (hrT1D : AllD rT1) :
  let '(bRh, bRt, bD0) := putBackD3K a0 rem rH1 rT1 d1 in
  AllPos bRh /\ AllPos bRt /\ AllD bRt /\
  evalR bRh bRt bD0 = npow (D_word a0) rem *> evalR rH1 rT1 d1.
Proof.
  unfold putBackD3K.
  destruct rH1 as [| rh0 rhRest].
  - destruct rT1 as [| rt0 rtRest].
    + destruct (N.eqb a0 0) eqn:ha0.
      * apply N.eqb_eq in ha0; subst a0.
        split_and; try exact I.
        unfold evalR; simpl.
        replace (d1 + rem) with (rem + d1) by lia.
        rewrite npow_append_npow. reflexivity.
      * pose proof (pushRDK_spec a0 rem [] [] d1 I I I) as hp.
        destruct (pushRDK a0 rem [] []) as [pRh pRt]; exact hp.
    + pose proof (pushRDK_spec a0 rem [] (rt0 :: rtRest) d1 I hrT1P hrT1D) as hp.
      destruct (pushRDK a0 rem [] (rt0 :: rtRest)) as [pRh pRt]; exact hp.
  - pose proof (pushRDK_spec a0 rem (rh0 :: rhRest) rT1 d1 hrH1P hrT1P hrT1D) as hp.
    destruct (pushRDK a0 rem (rh0 :: rhRest) rT1) as [pRh pRt]; exact hp.
Qed.

Lemma evalRuns_rev_decD (j kj : N) (dp' : Runs) (tail : side) (hkj : 1 <= kj) :
  evalRuns (rev (mkRun (SD j) kj :: dp')) tail =
  evalRuns (rev (decRunK (SD j) kj dp')) (D_word j *> tail).
Proof.
  unfold decRunK.
  destruct (N.leb kj 1) eqn:hle.
  - apply N.leb_le in hle; replace kj with 1 by lia.
    simpl rev; rewrite evalRuns_append; cbn [evalRuns evalSym].
    rewrite npow_1. reflexivity.
  - apply N.leb_gt in hle.
    simpl rev; rewrite !evalRuns_append; simpl evalRuns.
    replace kj with ((kj - 1) + 1) at 1 by lia.
    rewrite <- npow_succ_right, Str_app_assoc. reflexivity.
Qed.

Lemma doCallsNoneK_sound (Rh Rt : Runs) (d0 h : N) (allowDef : bool)
  (hh : 1 <= h) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt) :
  let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 h allowDef in
  AllPos nRh /\ AllPos nRt /\ AllD nRt /\ hd <= h /\
  NCalls hd (evalR Rh Rt d0) (evalR nRh nRt nD0).
Proof.
  pose proof (splitDPrefixK_spec Rh (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) hRh) as hsp.
  unfold doCallsNoneK.
  destruct (splitDPrefixK Rh) as [dpref rtail].
  destruct hsp as [hdpP [hdpD [hrtP hspE]]].
  assert (hzero : AllPos Rh /\ AllPos Rt /\ AllD Rt /\ 0 <= h /\
    NCalls 0 (evalR Rh Rt d0) (evalR Rh Rt d0)).
  { split_and; try assumption; [lia | apply NCalls_zero]. }
  destruct (w10SplitK rtail) as [restH |] eqn:hw; [| exact hzero].
  assert (hw10 : AllPos restH /\
    evalRuns rtail (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) = [S1; S0] *> evalR restH Rt d0).
  { unfold w10SplitK in hw.
    destruct rtail as [| [w1 k1] rt1]; [discriminate |].
    destruct w1; try discriminate.
    - destruct (N.eqb k1 1) eqn:hk1.
      + apply N.eqb_eq in hk1; subst k1.
        destruct rt1 as [| [w2 k2] rt2]; [discriminate |].
        destruct w2; try discriminate.
        destruct (N.eqb k2 1) eqn:hk2.
        * apply N.eqb_eq in hk2; subst k2. inversion hw; subst.
          split; [exact (proj2 (proj2 hrtP)) |].
          simpl; rewrite ?npow_1. reflexivity.
        * destruct k2 as [| [p|p|]]; try discriminate; exfalso; apply N.eqb_neq in hk2; lia.
      + destruct k1 as [| [p|p|]]; try discriminate; exfalso; apply N.eqb_neq in hk1; lia.
    - destruct (N.eqb k1 1) eqn:hk1.
      + apply N.eqb_eq in hk1; subst k1. inversion hw; subst.
        split; [exact (proj2 hrtP) |].
        simpl; rewrite ?npow_1. reflexivity.
      + destruct k1 as [| [p|p|]]; try discriminate; exfalso; apply N.eqb_neq in hk1; lia. }
  destruct hw10 as [hrestHP hw10E].
  assert (hR0 : evalR Rh Rt d0 = evalRuns (rev dpref) ([S1; S0] *> evalR restH Rt d0)).
  { unfold evalR in hspE |- *; rewrite hspE, hw10E; reflexivity. }
  destruct (peekHeadD3K restH Rt d0) as [[[[[a0 k0] rH1] rT1] d1] |] eqn:hpk; [| exact hzero].
  destruct (peekHeadD3K_spec restH Rt d0 a0 k0 d1 rH1 rT1 hrestHP hRt hD hpk)
    as [hk0 [hrH1P [hrT1P [hrT1D hpkE]]]].
  destruct (doCallsRes1K dpref a0 k0 h rH1 rT1 d1) as [[[[hd1 nRh1] nRt1] nD1] |] eqn:hres1.
  - unfold doCallsRes1K in hres1.
    destruct dpref as [| [wdp kj] dp']; [discriminate |].
    destruct wdp; try discriminate.
    rename n into j.
    destruct (N.eqb a0 0) eqn:ha0; [| discriminate].
    apply N.eqb_eq in ha0; subst a0.
    destruct (N.leb 2 k0) eqn:hk2; [| discriminate].
    apply N.leb_le in hk2.
    set (avail0 := N.div2 k0) in *.
    set (avail := if N.leb avail0 h then avail0 else h) in *.
    assert (hav_le : avail <= h /\ 2 * avail <= k0 /\ 1 <= avail).
    { unfold avail, avail0. rewrite N.div2_div.
      destruct (N.leb (k0 / 2) h) eqn:hle;
        [apply N.leb_le in hle | apply N.leb_gt in hle]; lia. }
    destruct hav_le as [hav_h [hav_k0 hav_pos]].
    set (rem := k0 - 2 * avail) in *.
    pose proof (putBackD3K_spec 0 rem rH1 rT1 d1 hrH1P hrT1P hrT1D) as hpb.
    destruct (putBackD3K 0 rem rH1 rT1 d1) as [[bRh bRt] bD0].
    destruct hpb as [hbRhP [hbRtP [hbRtD hpbE]]].
    set (bRh1 := pushRunK Sw10 1 bRh) in *.
    pose proof (pushRDK_spec 2 1 bRh1 bRt bD0 (AllPos_pushRunK Sw10 1 hbRhP) hbRtP hbRtD) as hp2.
    destruct (pushRDK 2 1 bRh1 bRt) as [bRh2 bRt2].
    destruct hp2 as [p2 [q2 [d2h e2]]].
    pose proof (pushRDK_spec 3 (avail - 1) bRh2 bRt2 bD0 p2 q2 d2h) as hp3.
    destruct (pushRDK 3 (avail - 1) bRh2 bRt2) as [bRh3 bRt3].
    destruct hp3 as [p3 [q3 [d3h e3]]].
    pose proof (pushRDK_spec (j + 1) 1 bRh3 bRt3 bD0 p3 q3 d3h) as hp4.
    destruct (pushRDK (j + 1) 1 bRh3 bRt3) as [bRh4 bRt4].
    destruct hp4 as [p4 [q4 [d4h e4]]].
    pose proof (restoreDPrefK_spec (decRunK (SD j) kj dp') bRh4 bRt4 bD0
      (AllPos_decRunK (SD j) kj (proj2 hdpP)) (AllD_decRunK j kj hdpD) p4 q4 d4h) as hrest.
    destruct (restoreDPrefK (decRunK (SD j) kj dp') bRh4 bRt4) as [nRh nRt].
    inversion hres1; subst.
    destruct hrest as [pr1 [qr1 [dr1 er1]]].
    split_and; [exact pr1 | exact qr1 | exact dr1 | exact hav_h |].
    rewrite hR0, (evalRuns_rev_decD j kj dp' _ (proj1 hdpP)), er1.
    apply (NCalls_prepend_allD (rev (decRunK (SD j) kj dp')) (AllD_rev (AllD_decRunK j kj hdpD))).
    rewrite hpkE, e4, e3, e2.
    assert (hb1E : evalR bRh1 bRt nD1 = [S1; S0] *> evalR bRh bRt nD1).
    { unfold evalR, bRh1; rewrite evalRuns_pushRunK, npow_1; reflexivity. }
    rewrite !npow_1, hb1E.
    replace k0 with (2 * avail + rem) by lia.
    rewrite <- npow_append_npow, <- hpbE.
    pose proof (NCalls_collide_pow (avail - 1) j (evalR bRh bRt nD1)) as hcoll.
    replace (avail - 1 + 1) with avail in hcoll by lia.
    exact hcoll.
  - clear hres1.
    destruct allowDef; [| exact hzero].
    destruct (doCallsRes2K dpref a0 k0 rH1 rT1 d1) as [[[[hd2 nRh2] nRt2] nD2] |] eqn:hres2.
    + unfold doCallsRes2K in hres2.
      destruct dpref as [| [wdp kj] dp']; [discriminate |].
      destruct wdp; try discriminate.
      rename n into j.
      destruct (N.eqb a0 0) eqn:ha0; [| discriminate].
      apply N.eqb_eq in ha0; subst a0.
      destruct (N.eqb k0 1) eqn:hk1; [| discriminate].
      apply N.eqb_eq in hk1; subst k0.
      destruct (popOneD3K rH1 rT1 d1) as [[[[d rH2] rT2] d2] |] eqn:hpop; [| discriminate].
      destruct (popOneD3K_spec rH1 rT1 rH2 rT2 d1 d d2 hrH1P hrT1P hrT1D hpop) as [p2 [q2 [d2h e2]]].
      set (bRh1 := pushRunK Sw10 1 rH2) in *.
      pose proof (pushRDK_spec (d + 2) 1 bRh1 rT2 d2 (AllPos_pushRunK Sw10 1 p2) q2 d2h) as hp2.
      destruct (pushRDK (d + 2) 1 bRh1 rT2) as [bRh2 bRt2].
      destruct hp2 as [p3 [q3 [d3h e3]]].
      pose proof (pushRDK_spec (j + 1) 1 bRh2 bRt2 d2 p3 q3 d3h) as hp3.
      destruct (pushRDK (j + 1) 1 bRh2 bRt2) as [bRh3 bRt3].
      destruct hp3 as [p4 [q4 [d4h e4]]].
      pose proof (restoreDPrefK_spec (decRunK (SD j) kj dp') bRh3 bRt3 d2
        (AllPos_decRunK (SD j) kj (proj2 hdpP)) (AllD_decRunK j kj hdpD) p4 q4 d4h) as hrest.
      destruct (restoreDPrefK (decRunK (SD j) kj dp') bRh3 bRt3) as [nRh nRt].
      inversion hres2; subst.
      destruct hrest as [pr1 [qr1 [dr1 er1]]].
      split_and; [exact pr1 | exact qr1 | exact dr1 | exact hh |].
      rewrite hR0, (evalRuns_rev_decD j kj dp' _ (proj1 hdpP)), er1.
      apply (NCalls_prepend_allD (rev (decRunK (SD j) kj dp')) (AllD_rev (AllD_decRunK j kj hdpD))).
      rewrite hpkE, e2, e4, e3, !npow_1.
      assert (hb1E : evalR bRh1 rT2 nD2 = [S1; S0] *> evalR rH2 rT2 nD2).
      { unfold evalR, bRh1; rewrite evalRuns_pushRunK, npow_1; reflexivity. }
      rewrite hb1E.
      exact (NCalls_succ (OneCall_defect0 j d (evalR rH2 rT2 nD2)) (NCalls_zero _)).
    + clear hres2.
      destruct (N.eqb a0 1) eqn:ha1; [| exact hzero].
      apply N.eqb_eq in ha1; subst a0.
      destruct (N.leb 2 k0) eqn:hk2.
      * apply N.leb_le in hk2.
        pose proof (putBackD3K_spec 1 (k0 - 2) rH1 rT1 d1 hrH1P hrT1P hrT1D) as hpb.
        destruct (putBackD3K 1 (k0 - 2) rH1 rT1 d1) as [[bRh bRt] bD0].
        destruct hpb as [hbRhP [hbRtP [hbRtD hpbE]]].
        set (bRh1 := pushRunK Sw10 1 bRh).
        pose proof (pushRDK_spec 2 1 bRh1 bRt bD0 (AllPos_pushRunK Sw10 1 hbRhP) hbRtP hbRtD) as hp2.
        destruct (pushRDK 2 1 bRh1 bRt) as [bRh2 bRt2].
        destruct hp2 as [p3 [q3 [d3h e3]]].
        pose proof (pushRDK_spec 0 2 bRh2 bRt2 bD0 p3 q3 d3h) as hp3.
        destruct (pushRDK 0 2 bRh2 bRt2) as [bRh3 bRt3].
        destruct hp3 as [p4 [q4 [d4h e4]]].
        pose proof (restoreDPrefK_spec dpref bRh3 bRt3 bD0 hdpP hdpD p4 q4 d4h) as hrest.
        destruct (restoreDPrefK dpref bRh3 bRt3) as [nRh nRt].
        destruct hrest as [pr1 [qr1 [dr1 er1]]].
        split_and; [exact pr1 | exact qr1 | exact dr1 | exact hh |].
        rewrite hR0, er1.
        apply (NCalls_prepend_allD (rev dpref) (AllD_rev hdpD)).
        rewrite hpkE, e4, e3, npow_2, npow_1, Str_app_assoc.
        assert (hb1E : evalR bRh1 bRt bD0 = [S1; S0] *> evalR bRh bRt bD0).
        { unfold evalR, bRh1; rewrite evalRuns_pushRunK, npow_1; reflexivity. }
        rewrite hb1E.
        replace k0 with (2 + (k0 - 2)) at 1 by lia.
        rewrite npow_two_add, !Str_app_assoc, <- hpbE.
        exact (NCalls_succ (OneCall_defect1 1 (evalR bRh bRt bD0)) (NCalls_zero _)).
      * apply N.leb_gt in hk2.
        replace k0 with 1 in hpkE by lia.
        destruct (popOneD3K rH1 rT1 d1) as [[[[d rH2] rT2] d2] |] eqn:hpop; [| exact hzero].
        destruct (popOneD3K_spec rH1 rT1 rH2 rT2 d1 d d2 hrH1P hrT1P hrT1D hpop) as [p2 [q2 [d2h e2]]].
        set (bRh1 := pushRunK Sw10 1 rH2).
        pose proof (pushRDK_spec (d + 1) 1 bRh1 rT2 d2 (AllPos_pushRunK Sw10 1 p2) q2 d2h) as hp2.
        destruct (pushRDK (d + 1) 1 bRh1 rT2) as [bRh2 bRt2].
        destruct hp2 as [p3 [q3 [d3h e3]]].
        pose proof (pushRDK_spec 0 2 bRh2 bRt2 d2 p3 q3 d3h) as hp3.
        destruct (pushRDK 0 2 bRh2 bRt2) as [bRh3 bRt3].
        destruct hp3 as [p4 [q4 [d4h e4]]].
        pose proof (restoreDPrefK_spec dpref bRh3 bRt3 d2 hdpP hdpD p4 q4 d4h) as hrest.
        destruct (restoreDPrefK dpref bRh3 bRt3) as [nRh nRt].
        destruct hrest as [pr1 [qr1 [dr1 er1]]].
        split_and; [exact pr1 | exact qr1 | exact dr1 | exact hh |].
        rewrite hR0, er1.
        apply (NCalls_prepend_allD (rev dpref) (AllD_rev hdpD)).
        rewrite hpkE, e2, e4, e3, npow_2, !npow_1, Str_app_assoc.
        assert (hb1E : evalR bRh1 rT2 d2 = [S1; S0] *> evalR rH2 rT2 d2).
        { unfold evalR, bRh1; rewrite evalRuns_pushRunK, npow_1; reflexivity. }
        rewrite hb1E.
        exact (NCalls_succ (OneCall_defect1 d (evalR rH2 rT2 d2)) (NCalls_zero _)).
Qed.

Lemma sweepDK_spec (L Rh : Runs) (tail : side) (hL : AllPos L) (hRh : AllPos Rh) :
  let '(L', Rh') := sweepDK L Rh in
  AllPos L' /\ AllPos Rh' /\
  CfgR (evalRuns L 0inf) (evalRuns Rh tail) -->* CfgR (evalRuns L' 0inf) (evalRuns Rh' tail).
Proof.
  revert L hL.
  induction Rh as [| [w k] rest ih]; intros L hL.
  - exact (conj hL (conj I (evstep_refl tm _))).
  - destruct w; try exact (conj hL (conj hRh (evstep_refl tm _))).
    cbn [sweepDK].
    pose proof (ih (proj2 hRh) (pushSK n k L) (AllPos_pushSK n k hL)) as hrec.
    destruct (sweepDK (pushSK n k L) rest) as [L' Rh'].
    destruct hrec as [p1 [p2 hreach]].
    split_and; [exact p1 | exact p2 |].
    cbn [evalRuns]; unfold evalSym.
    eapply evstep_trans; [apply (rule_right_pow (evalRuns L 0inf) (evalRuns rest tail) n k) |].
    rewrite <- evalRuns_pushSK. exact hreach.
Qed.

Lemma sweepSK_spec (L Rh Rt : Runs) (d0 : N)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt) :
  let '(L', Rh', Rt') := sweepSK L Rh Rt in
  AllPos L' /\ AllPos Rh' /\ AllPos Rt' /\ AllD Rt' /\
  CfgL (evalRuns L 0inf) (evalR Rh Rt d0) -->* CfgL (evalRuns L' 0inf) (evalR Rh' Rt' d0).
Proof.
  revert Rh Rt hRh hRt hD.
  induction L as [| [w k] rest ih]; intros Rh Rt hRh hRt hD.
  - exact (conj I (conj hRh (conj hRt (conj hD (evstep_refl tm _))))).
  - destruct w; try exact (conj hL (conj hRh (conj hRt (conj hD (evstep_refl tm _))))).
    cbn [sweepSK].
    pose proof (pushRDK_spec n k Rh Rt d0 hRh hRt hD) as hp.
    destruct (pushRDK n k Rh Rt) as [Rh1 Rt1].
    destruct hp as [p1 [q1 [d1 e1]]].
    pose proof (ih (proj2 hL) Rh1 Rt1 p1 q1 d1) as hrec.
    destruct (sweepSK rest Rh1 Rt1) as [[L' Rh'] Rt'].
    destruct hrec as [a1 [a2 [a3 [a4 hreach]]]].
    split_and; [exact a1 | exact a2 | exact a3 | exact a4 |].
    cbn [evalRuns]; unfold evalSym.
    eapply evstep_trans; [apply (rule_left_pow (evalRuns rest 0inf) (evalR Rh Rt d0) n k) |].
    rewrite <- e1. exact hreach.
Qed.

(* ========================================================================== *)
(* Section 4: Loop Soundness & Step Soundness (MR, ML, MJ, stepK)             *)
(* ========================================================================== *)

Ltac split_opt h cfg_sub hsub :=
  lazymatch type of h with
  | match ?E with Some _ => _ | None => _ end = Some _ =>
    destruct E as [cfg_sub |] eqn:hsub;
    [inversion h; subst cfg_sub; clear h | clear hsub]
  end.

Lemma evalRuns_B_unpack (ba bc : N) (L1 : Runs) (tail : side) :
  evalRuns (pushRunK Sw10 ba (pushRunK Sb1 bc (pushRunK (SS 0) 2 L1))) tail =
  B_word ba bc *> evalRuns L1 tail.
Proof.
  rewrite !evalRuns_pushRunK, npow_2.
  unfold evalSym, B_word. rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma evalR_nil_pushDK (n k : N) (Rt : Runs) (d0 : N) :
  evalR [] (pushDK n k Rt) d0 = npow (D_word n) k *> evalR [] Rt d0.
Proof.
  unfold evalR; cbn [evalRuns]; rewrite evalRuns_pushDK. reflexivity.
Qed.

Lemma evalR_pushRunK (w : WSym) (k : N) (Rh Rt : Runs) (d0 : N) :
  evalR (pushRunK w k Rh) Rt d0 = npow (evalSym w) k *> evalR Rh Rt d0.
Proof.
  unfold evalR; rewrite evalRuns_pushRunK. reflexivity.
Qed.

Lemma w11_absorb_D_word (k01 dn : N) (r : side) :
  npow [S1; S1] k01 *> (D_word dn *> r) = D_word (dn + k01) *> r.
Proof.
  unfold D_word.
  rewrite !Str_app_assoc; cbn [Str_app].
  rewrite rot_11, npow_append_npow.
  replace (k01 + dn) with (dn + k01) by lia.
  reflexivity.
Qed.

Lemma dtail_stop_sound (did : bool) (m : Mode) (L Rt : Runs) (d : N) (cfg' : FastCfg)
  (hL : AllPos L) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : (if did then Some (mkCfg m L [] Rt d) else None) = Some cfg') :
  ValidCfg cfg' /\ evalCfg (mkCfg m L [] Rt d) -->* evalCfg cfg'.
Proof.
  destruct did; [inversion h; subst | discriminate].
  exact (conj (conj hL (conj I (conj hRt hD))) (evstep_refl tm _)).
Qed.

Lemma runDtailLoopAux_sound (fuel : nat) :
  forall (did : bool) (m : Mode) (L Rt : Runs) (d : N) (cfg' : FastCfg)
    (hL : AllPos L) (hRt : AllPos Rt) (hD : AllD Rt)
    (h : runDtailLoopAux fuel did m L Rt d = Some cfg'),
    ValidCfg cfg' /\ evalCfg (mkCfg m L [] Rt d) -->* evalCfg cfg'.
Proof.
  induction fuel as [| fuel' ih]; intros did m L Rt d cfg' hL hRt hD h.
  - cbn [runDtailLoopAux] in h.
    exact (dtail_stop_sound did m L Rt d cfg' hL hRt hD h).
  - cbn [runDtailLoopAux] in h.
    destruct L as [| [w k] L']; [exact (dtail_stop_sound did m [] Rt d cfg' I hRt hD h) |].
    destruct w as [n | n | a c | | | | | | | |];
      try exact (dtail_stop_sound did m _ Rt d cfg' hL hRt hD h).
    + destruct m.
      * exact (dtail_stop_sound did MR _ Rt d cfg' hL hRt hD h).
      * destruct (ih true ML L' (pushDK n k Rt) d cfg' (proj2 hL)
          (AllPos_pushDK n k hRt) (AllD_pushDK n k hD) h) as [hv hr].
        split; [exact hv |].
        unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns evalSym] in *.
        eapply evstep_trans; [apply (rule_left_pow (evalRuns L' 0inf) (evalR [] Rt d) n k) |].
        rewrite <- evalR_nil_pushDK. exact hr.
      * destruct (ih true ML (decRunK (SS n) k L') (pushDK (n + 1) 1 Rt) d cfg'
          (AllPos_decRunK (SS n) k (proj2 hL))
          (AllPos_pushDK (n + 1) 1 hRt) (AllD_pushDK (n + 1) 1 hD) h) as [hv hr].
        split; [exact hv |].
        pose proof (evalRuns_decRunK (SS n) k L' 0inf (proj1 hL)) as hdec.
        unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns] in *.
        rewrite <- hdec; unfold evalSym.
        eapply evstep_trans; [apply (rule_leftJ (evalRuns (decRunK (SS n) k L') 0inf) (evalR [] Rt d) n) |].
        replace (1 + n) with (n + 1) by lia.
        rewrite <- (npow_1 (D_word (n + 1))), <- evalR_nil_pushDK. exact hr.
    + destruct (N.leb 1 a) eqn:ha; [| exact (dtail_stop_sound did m _ Rt d cfg' hL hRt hD h)].
      apply N.leb_le in ha.
      destruct m.
      * exact (dtail_stop_sound did MR _ Rt d cfg' hL hRt hD h).
      * (* ML *)
        destruct (N.eqb (c mod 3) 2) eqn:hr2.
        -- apply N.eqb_eq in hr2.
           set (qv := c / 3) in *.
           set (nd := d + 2 * (k * (qv + 1))) in *.
           set (Rt1 := pushDK (a + 1) (k - 1) (pushDK a 1 Rt)) in *.
           destruct (ih true MJ L' Rt1 nd cfg' (proj2 hL)
             (AllPos_pushDK (a + 1) (k - 1) (AllPos_pushDK a 1 hRt))
             (AllD_pushDK (a + 1) (k - 1) (AllD_pushDK a 1 hD)) h) as [hv hreach].
           split; [exact hv |].
           pose proof (proj1 hL) as hk.
           pose proof (NCalls_pureD_tail Rt hD (k * (qv + 1)) d) as hc.
           change (d + 2 * (k * (qv + 1))) with nd in hc.
           replace k with (1 + (k - 1)) in hc by lia.
           pose proof (B_word_ML_r2_pow (a - 1) qv (k - 1) (evalRuns L' 0inf)
             (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
           replace (1 + (a - 1)) with a in hstep by lia.
           replace (2 + (a - 1)) with (a + 1) in hstep by lia.
           replace (3 * qv + 2) with c in hstep by (unfold qv; lia).
           replace (1 + (k - 1)) with k in hstep by lia.
           unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns evalSym] in *.
           eapply evstep_trans; [exact hstep |].
           unfold Rt1 in hreach; rewrite !evalR_nil_pushDK, npow_1 in hreach.
           exact hreach.
        -- apply N.eqb_neq in hr2.
           set (qv := c / 3) in *.
           set (nd := d + 2 * qv) in *.
           set (L1 := decRunK (SB a c) k L') in *.
           pose proof (evalRuns_decRunK (SB a c) k L' 0inf (proj1 hL)) as hdec.
           pose proof (NCalls_pureD_tail Rt hD qv d) as hc.
           destruct (N.eqb (c mod 3) 0) eqn:hr0.
           ++ apply N.eqb_eq in hr0.
              set (Rt1 := pushDK 0 1 (pushDK a 1 Rt)) in *.
              destruct (ih true ML L1 Rt1 nd cfg'
                (AllPos_decRunK (SB a c) k (proj2 hL))
                (AllPos_pushDK 0 1 (AllPos_pushDK a 1 hRt))
                (AllD_pushDK 0 1 (AllD_pushDK a 1 hD)) h) as [hv hreach].
              split; [exact hv |].
              pose proof (B_word_ML_r0 (a - 1) qv (evalRuns L1 0inf)
                (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
              replace (1 + (a - 1)) with a in hstep by lia.
              replace (3 * qv) with c in hstep by (unfold qv; lia).
              unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns] in *.
              rewrite <- hdec; unfold evalSym.
              eapply evstep_trans; [exact hstep |].
              unfold Rt1 in hreach; rewrite !evalR_nil_pushDK, !npow_1 in hreach.
              exact hreach.
           ++ apply N.eqb_neq in hr0.
              set (Rt1 := pushDK 0 2 (pushDK (a - 1) 1 Rt)) in *.
              destruct (ih true ML L1 Rt1 nd cfg'
                (AllPos_decRunK (SB a c) k (proj2 hL))
                (AllPos_pushDK 0 2 (AllPos_pushDK (a - 1) 1 hRt))
                (AllD_pushDK 0 2 (AllD_pushDK (a - 1) 1 hD)) h) as [hv hreach].
              split; [exact hv |].
              pose proof (B_word_ML_r1 (a - 1) qv (evalRuns L1 0inf)
                (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
              replace (1 + (a - 1)) with a in hstep by lia.
              replace (3 * qv + 1) with c in hstep by (unfold qv; lia).
              unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns] in *.
              rewrite <- hdec; unfold evalSym.
              eapply evstep_trans; [exact hstep |].
              unfold Rt1 in hreach; rewrite !evalR_nil_pushDK, npow_2, npow_1, Str_app_assoc in hreach.
              exact hreach.
      * (* MJ *)
        destruct (N.eqb (c mod 3) 2) eqn:hr2.
        -- apply N.eqb_eq in hr2.
           set (qv := c / 3) in *.
           set (nd := d + 2 * (k * (qv + 1))) in *.
           set (Rt1 := pushDK (a + 1) k Rt) in *.
           destruct (ih true MJ L' Rt1 nd cfg' (proj2 hL)
             (AllPos_pushDK (a + 1) k hRt) (AllD_pushDK (a + 1) k hD) h) as [hv hreach].
           split; [exact hv |].
           pose proof (NCalls_pureD_tail Rt hD (k * (qv + 1)) d) as hc.
           pose proof (B_word_MJ_r2_pow (a - 1) qv k (evalRuns L' 0inf)
             (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
           replace (1 + (a - 1)) with a in hstep by lia.
           replace (2 + (a - 1)) with (a + 1) in hstep by lia.
           replace (3 * qv + 2) with c in hstep by (unfold qv; lia).
           unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns evalSym] in *.
           eapply evstep_trans; [exact hstep |].
           unfold Rt1 in hreach; rewrite evalR_nil_pushDK in hreach.
           exact hreach.
        -- apply N.eqb_neq in hr2.
           destruct (N.leb 3 c) eqn:hc3; [| exact (dtail_stop_sound did MJ _ Rt d cfg' hL hRt hD h)].
           apply N.leb_le in hc3.
           set (qv := c / 3) in *.
           assert (hqv1 : 1 <= qv) by (unfold qv; lia).
           set (nd := d + 2 * qv) in *.
           set (L1 := decRunK (SB a c) k L') in *.
           pose proof (evalRuns_decRunK (SB a c) k L' 0inf (proj1 hL)) as hdec.
           pose proof (NCalls_pureD_tail Rt hD qv d) as hc.
           change (d + 2 * qv) with nd in hc.
           replace qv with ((qv - 1) + 1) in hc by lia.
           destruct (N.eqb (c mod 3) 0) eqn:hr0.
           ++ apply N.eqb_eq in hr0.
              set (Rt1 := pushDK 0 1 (pushDK (a + 1) 1 Rt)) in *.
              destruct (ih true ML L1 Rt1 nd cfg'
                (AllPos_decRunK (SB a c) k (proj2 hL))
                (AllPos_pushDK 0 1 (AllPos_pushDK (a + 1) 1 hRt))
                (AllD_pushDK 0 1 (AllD_pushDK (a + 1) 1 hD)) h) as [hv hreach].
              split; [exact hv |].
              pose proof (B_word_MJ_r0 (a - 1) (qv - 1) (evalRuns L1 0inf)
                (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
              replace (1 + (a - 1)) with a in hstep by lia.
              replace (2 + (a - 1)) with (a + 1) in hstep by lia.
              replace (3 * (qv - 1 + 1)) with c in hstep by (unfold qv; lia).
              unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns] in *.
              rewrite <- hdec; unfold evalSym.
              eapply evstep_trans; [exact hstep |].
              unfold Rt1 in hreach; rewrite !evalR_nil_pushDK, !npow_1 in hreach.
              exact hreach.
           ++ apply N.eqb_neq in hr0.
              set (Rt1 := pushDK 0 2 (pushDK a 1 Rt)) in *.
              destruct (ih true ML L1 Rt1 nd cfg'
                (AllPos_decRunK (SB a c) k (proj2 hL))
                (AllPos_pushDK 0 2 (AllPos_pushDK a 1 hRt))
                (AllD_pushDK 0 2 (AllD_pushDK a 1 hD)) h) as [hv hreach].
              split; [exact hv |].
              pose proof (B_word_MJ_r1 (a - 1) (qv - 1) (evalRuns L1 0inf)
                (evalR [] Rt d) (evalR [] Rt nd) hc) as hstep.
              replace (1 + (a - 1)) with a in hstep by lia.
              replace (3 * (qv - 1 + 1) + 1) with c in hstep by (unfold qv; lia).
              unfold evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns] in *.
              rewrite <- hdec; unfold evalSym.
              eapply evstep_trans; [exact hstep |].
              unfold Rt1 in hreach; rewrite !evalR_nil_pushDK, npow_2, npow_1, Str_app_assoc in hreach.
              exact hreach.
Qed.

Lemma runDtailLoopK_sound (f4096 : nat) (m0 : Mode) (L0 Rt0 : Runs) (d0 : N) (cfg' : FastCfg)
  (hL : AllPos L0) (hRt : AllPos Rt0) (hD : AllD Rt0)
  (h : runDtailLoopK f4096 m0 L0 Rt0 d0 = Some cfg') :
  ValidCfg cfg' /\ evalCfg (mkCfg m0 L0 [] Rt0 d0) -->* evalCfg cfg'.
Proof.
  exact (runDtailLoopAux_sound f4096 false m0 L0 Rt0 d0 cfg' hL hRt hD h).
Qed.

Lemma stopMr_sound (did : bool) (L Rh Rt : Runs) (d : N) (cfg' : FastCfg)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : stopMr did L Rh Rt d = Some cfg') :
  ValidCfg cfg' /\ CfgR (evalRuns L 0inf) ([S1; S0] *> evalR Rh Rt d) -->* evalCfg cfg'.
Proof.
  unfold stopMr in h.
  destruct did; [inversion h; subst | discriminate].
  split; [exact (conj hL (conj (AllPos_pushRunK Sw10 1 hRh) (conj hRt hD))) |].
  unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
  rewrite evalR_pushRunK, npow_1; unfold evalSym.
  exact (evstep_refl tm _).
Qed.

Lemma stepMrW10WithD_sound
  (go : bool -> Runs -> Runs -> Runs -> N -> option FastCfg)
  (hgo : forall did' L' Rh' Rt' d' cfg',
    AllPos L' -> AllPos Rh' -> AllPos Rt' -> AllD Rt' ->
    go did' L' Rh' Rt' d' = Some cfg' ->
    ValidCfg cfg' /\ CfgR (evalRuns L' 0inf) ([S1; S0] *> evalR Rh' Rt' d') -->* evalCfg cfg')
  (did : bool) (L Rh Rt : Runs) (d a ka : N) (Rh1 Rt1 : Runs) (d1 : N) (isRh : bool) (cfg' : FastCfg)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (hka : 1 <= ka) (hRh1 : AllPos Rh1) (hRt1 : AllPos Rt1) (hD1 : AllD Rt1)
  (hisRh : isRh = false -> Rh1 = [])
  (hsplit : evalR Rh Rt d = npow (D_word a) ka *> evalR Rh1 Rt1 d1)
  (h : stepMrW10WithD go did L Rh Rt d a ka Rh1 Rt1 d1 isRh = Some cfg') :
  ValidCfg cfg' /\ CfgR (evalRuns L 0inf) ([S1; S0] *> evalR Rh Rt d) -->* evalCfg cfg'.
Proof.
  unfold stepMrW10WithD in h.
  destruct (if N.leb 2 a then N.leb 2 ka else false) eqn:hpair.
  - destruct (N.leb 2 a) eqn:ha2; [| discriminate].
    apply N.leb_le in ha2; apply N.leb_le in hpair.
    set (kp := N.div2 ka) in *.
    set (rem := N.b2n (N.odd ka)) in *.
    assert (hN :
      let '(RhN, RtN) := if isRh then (pushDK a rem Rh1, Rt1) else (Rh1, pushDK a rem Rt1) in
      AllPos RhN /\ AllPos RtN /\ AllD RtN /\
      evalR RhN RtN d1 = npow (D_word a) rem *> evalR Rh1 Rt1 d1).
    { destruct isRh.
      - split_and; [exact (AllPos_pushDK a rem hRh1) | exact hRt1 | exact hD1 |].
        exact (evalR_pushRunK (SD a) rem Rh1 Rt1 d1).
      - rewrite (hisRh eq_refl).
        split_and; [exact I | exact (AllPos_pushDK a rem hRt1) | exact (AllD_pushDK a rem hD1) |].
        exact (evalR_nil_pushDK a rem Rt1 d1). }
    destruct (if isRh then (pushDK a rem Rh1, Rt1) else (Rh1, pushDK a rem Rt1)) as [RhN RtN].
    destruct hN as [pN [qN [dN eN]]].
    destruct (hgo true (pushBK (a + 2) (2 * (a - 2)) kp L) RhN RtN d1 cfg'
      (AllPos_pushBK (a + 2) (2 * (a - 2)) kp hL) pN qN dN h) as [hv hreach].
    split; [exact hv |].
    assert (hka_eq : ka = 2 * kp + rem).
    { unfold kp, rem; rewrite N.div2_div, N_b2n_odd_mod2; lia. }
    rewrite hsplit, hka_eq, <- npow_append_npow, <- eN.
    pose proof (rule_defect2_D_pair_pow (evalRuns L 0inf) (evalR RhN RtN d1) (a - 2) kp) as hstep.
    replace (2 + (a - 2)) with a in hstep by lia.
    replace (4 + (a - 2)) with (a + 2) in hstep by lia.
    eapply evstep_trans; [exact hstep |].
    rewrite evalRuns_pushBK in hreach. exact hreach.
  - destruct (N.eqb ka 1) eqn:hka1; [| exact (stopMr_sound did L Rh Rt d cfg' hL hRh hRt hD h)].
    apply N.eqb_eq in hka1; subst ka.
    destruct (popOneD3K Rh1 Rt1 d1) as [[[[m Rh2] Rt2] d2] |] eqn:hpop;
      [| exact (stopMr_sound did L Rh Rt d cfg' hL hRh hRt hD h)].
    destruct (popOneD3K_spec Rh1 Rt1 Rh2 Rt2 d1 m d2 hRh1 hRt1 hD1 hpop) as [p2 [q2 [d2h e2]]].
    assert (hR_am : evalR Rh Rt d = D_word a *> (D_word m *> evalR Rh2 Rt2 d2)).
    { rewrite hsplit, npow_1, e2. reflexivity. }
    destruct (N.eqb a 0) eqn:ha0.
    + apply N.eqb_eq in ha0; subst a.
      split_opt h csub hfused.
      * destruct L as [| [w bk] L']; [discriminate |].
        destruct w as [| | ba bc | | | | | | | |]; try discriminate.
        destruct (N.leb 1 ba) eqn:hba; [| discriminate].
        destruct (N.leb 3 bc) eqn:hbc; [| discriminate].
        apply N.leb_le in hba; apply N.leb_le in hbc.
        destruct (if N.eqb (bc mod 3) 2 then hasD0AtLeastK Rh2 Rt2 d2 (2 * (bc / 3 + 1)) else false);
          [discriminate |].
        set (L0' := decRunK (SB ba bc) bk L') in *.
        set (L1 := pushSK (m + 2) 1 (pushBK (ba + 1) (bc - 3) 1 L0')) in *.
        destruct (hgo true L1 Rh2 Rt2 d2 cfg'
          (AllPos_pushSK (m + 2) 1 (AllPos_pushBK (ba + 1) (bc - 3) 1
            (AllPos_decRunK (SB ba bc) bk (proj2 hL))))
          p2 q2 d2h hfused) as [hv hreach].
        split; [exact hv |].
        pose proof (evalRuns_decRunK (SB ba bc) bk L' 0inf (proj1 hL)) as hdec.
        cbn [evalRuns]; rewrite <- hdec, hR_am; unfold evalSym.
        eapply evstep_trans; [apply (B_word_MR_fused ba bc m hbc (evalRuns L0' 0inf) (evalR Rh2 Rt2 d2)) |].
        unfold L1 in hreach; rewrite evalRuns_pushSK, evalRuns_pushBK, !npow_1 in hreach.
        exact hreach.
      * pose proof (pushRDK_spec (m + 2) 1 (pushRunK Sw10 1 Rh2) Rt2 d2
          (AllPos_pushRunK Sw10 1 p2) q2 d2h) as hp4.
        destruct (pushRDK (m + 2) 1 (pushRunK Sw10 1 Rh2) Rt2) as [Rh4 Rt4].
        inversion h; subst.
        destruct hp4 as [p4 [q4 [d4h e4]]].
        split; [exact (conj hL (conj p4 (conj q4 d4h))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
        rewrite hR_am, e4, evalR_pushRunK, !npow_1; unfold evalSym.
        exact (rule_defect0_D (evalRuns L 0inf) (evalR Rh2 Rt2 d2) m).
    + apply N.eqb_neq in ha0.
      destruct (N.eqb a 1) eqn:ha1.
      * apply N.eqb_eq in ha1; subst a.
        pose proof (pushRDK_spec (m + 1) 1 (pushRunK Sw10 1 Rh2) Rt2 d2
          (AllPos_pushRunK Sw10 1 p2) q2 d2h) as hp4.
        destruct (pushRDK (m + 1) 1 (pushRunK Sw10 1 Rh2) Rt2) as [Rh4 Rt4].
        destruct hp4 as [p4 [q4 [d4h e4]]].
        pose proof (pushRDK_spec 0 2 Rh4 Rt4 d2 p4 q4 d4h) as hp5.
        destruct (pushRDK 0 2 Rh4 Rt4) as [Rh5 Rt5].
        inversion h; subst.
        destruct hp5 as [p5 [q5 [d5h e5]]].
        split; [exact (conj hL (conj p5 (conj q5 d5h))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
        rewrite hR_am, e5, e4, evalR_pushRunK, npow_2, !npow_1, Str_app_assoc; unfold evalSym.
        replace (m + 1) with (1 + m) by lia.
        exact (rule_defect1_D (evalRuns L 0inf) (evalR Rh2 Rt2 d2) m).
      * apply N.eqb_neq in ha1.
        destruct (hgo true (pushBK (m + 2) (2 * (a - 2)) 1 L) Rh2 Rt2 d2 cfg'
          (AllPos_pushBK (m + 2) (2 * (a - 2)) 1 hL) p2 q2 d2h h) as [hv hreach].
        split; [exact hv |].
        rewrite hR_am.
        pose proof (rule_defect2_D (evalRuns L 0inf) (evalR Rh2 Rt2 d2) (a - 2) m) as hstep.
        replace (2 + (a - 2)) with a in hstep by lia.
        replace (2 + m) with (m + 2) in hstep by lia.
        eapply evstep_trans; [exact hstep |].
        rewrite evalRuns_pushBK, npow_1 in hreach. exact hreach.
Qed.

Lemma runMrW10LoopAux_sound (fuel : nat) :
  forall (did : bool) (L Rh Rt : Runs) (d : N) (cfg' : FastCfg)
    (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
    (h : runMrW10LoopAux fuel did L Rh Rt d = Some cfg'),
    ValidCfg cfg' /\ CfgR (evalRuns L 0inf) ([S1; S0] *> evalR Rh Rt d) -->* evalCfg cfg'.
Proof.
  induction fuel as [| fuel' ih]; intros did L Rh Rt d cfg' hL hRh hRt hD h.
  - cbn [runMrW10LoopAux] in h.
    exact (stopMr_sound did L Rh Rt d cfg' hL hRh hRt hD h).
  - cbn [runMrW10LoopAux] in h.
    destruct Rh as [| [w ka] Rh1].
    + destruct Rt as [| [wt kt] Rt1].
      * destruct (N.eqb d 0) eqn:hd0.
        -- exact (stopMr_sound did L [] [] d cfg' hL I I I h).
        -- apply N.eqb_neq in hd0.
           assert (hdsplit : evalR [] [] d = npow (D_word 0) d *> evalR [] [] 0).
           { unfold evalR; cbn [evalRuns]; rewrite npow_0; cbn [Str_app]; reflexivity. }
           exact (stepMrW10WithD_sound (runMrW10LoopAux fuel') ih did L [] [] d 0 d [] [] 0 false cfg'
             hL I I I ltac:(lia) I I I (fun _ => eq_refl) hdsplit h).
      * destruct wt; try contradiction.
        exact (stepMrW10WithD_sound (runMrW10LoopAux fuel') ih did L [] (mkRun (SD n) kt :: Rt1) d n kt [] Rt1 d false cfg'
          hL I hRt hD (proj1 hRt) I (proj2 hRt) hD (fun _ => eq_refl) eq_refl h).
    + destruct w; try exact (stopMr_sound did L _ Rt d cfg' hL hRh hRt hD h).
      exact (stepMrW10WithD_sound (runMrW10LoopAux fuel') ih did L (mkRun (SD n) ka :: Rh1) Rt d n ka Rh1 Rt d true cfg'
        hL hRh hRt hD (proj1 hRh) (proj2 hRh) hRt hD ltac:(discriminate) eq_refl h).
Qed.

Lemma runMrW10LoopK_sound (f4096 : nat) (L0 Rh0 Rt0 : Runs) (d0 : N) (cfg' : FastCfg)
  (hL : AllPos L0) (hRh : AllPos Rh0) (hRt : AllPos Rt0) (hD : AllD Rt0)
  (h : runMrW10LoopK f4096 L0 Rh0 Rt0 d0 = Some cfg') :
  ValidCfg cfg' /\ CfgR (evalRuns L0 0inf) (evalR Rh0 Rt0 d0) -->* evalCfg cfg'.
Proof.
  unfold runMrW10LoopK in h.
  destruct Rh0 as [| [w k] rest0]; [discriminate |].
  destruct w; try discriminate.
  destruct (N.eqb k 1) eqn:hk1.
  - apply N.eqb_eq in hk1; subst k.
    destruct (match rest0 with
              | [] => match Rt0 with [] => negb (d0 =? 0) | _ :: _ => true end
              | mkRun (SD _) _ :: _ => true
              | _ => false
              end); [| discriminate].
    destruct (runMrW10LoopAux_sound f4096 false L0 rest0 Rt0 d0 cfg' hL (proj2 hRh) hRt hD h)
      as [hv hreach].
    split; [exact hv |].
    unfold evalR at 1; cbn [evalRuns]; unfold evalSym; rewrite npow_1.
    exact hreach.
  - destruct k as [| [p|p|]]; try discriminate; exfalso; apply N.eqb_neq in hk1; lia.
Qed.

Lemma stepMRK_sound (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) (cfg' : FastCfg)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : stepMRK f64 f4096 L Rh Rt d0 = Some cfg') :
  ValidCfg cfg' /\ CfgR (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg'.
Proof.
  unfold stepMRK in h.
  destruct Rh as [| [rw rk] rrest].
  - pose proof (take10RunsK_spec f64 L 0inf hL) as ht10.
    destruct (take10RunsK f64 L) as [b1 L1].
    destruct ht10 as [hpL1 heL1].
    destruct (N.eqb b1 0) eqn:hb1.
    + inversion h; subst.
      split; [exact (conj hL (conj I (conj hRt hD))) |].
      pose proof (NCalls_pureD_tail Rt hD 1 d0) as hc1.
      replace (d0 + 2 * 1) with (d0 + 2) in hc1 by lia.
      exact (OneCall_of_NCalls_one hc1 (evalRuns L 0inf)).
    + apply N.eqb_neq in hb1.
      pose proof (take111RunsK_spec L1 0inf hpL1) as ht111.
      destruct (take111RunsK L1) as [c111 L2].
      destruct ht111 as [hpL2 heL2].
      inversion h; subst.
      split; [exact (conj (AllPos_pushRunK Sw10 b1 hpL2) (conj I (conj hRt hD))) |].
      unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
      rewrite heL1, heL2, evalRuns_pushRunK; unfold evalSym.
      pose proof (NCalls_pureD_tail Rt hD (c111 + 1) d0) as hc.
      pose proof (NCalls_from_MR c111 (b1 - 1) (evalRuns L2 0inf)
        (evalR [] Rt d0) (evalR [] Rt (d0 + 2 * (c111 + 1))) hc) as hstep.
      replace (1 + (b1 - 1)) with b1 in hstep by lia.
      exact hstep.
  - split_opt h csub hloop.
    + exact (runMrW10LoopK_sound f4096 L (mkRun rw rk :: rrest) Rt d0 cfg' hL hRh hRt hD hloop).
    + set (Rh := mkRun rw rk :: rrest) in *.
      assert (hnonD :
        (let '(c10, Rh1a) := take10RunsK f64 Rh in
         let res10 :=
           if N.eqb c10 0 then None
           else
             let '(Rh1, Rt1) := normRK Rh1a Rt in
             if N.eqb (N.b2n (N.odd c10)) 1 then
               let odd3 :=
                 if N.eqb c10 3 then
                   match tryTakeDRK Rh1 Rt1 d0 with
                   | Some (dn, Rh2, Rt2, d2) =>
                     let L' := pushRunK Sw11 dn (pushRunK Sw1101 2 (pushRunK (SS 0) 1 L)) in
                     Some (mkCfg ML L' (pushRunK Sb1 1 Rh2) Rt2 d2)
                   | None => None
                   end
                 else None in
               match odd3 with
               | Some cfg => Some cfg
               | None =>
                 let Rh1' := pushRunK Sw10 (c10 - 1) Rh1 in
                 match tryTakeDRK Rh1' Rt1 d0 with
                 | None => None
                 | Some (a, Rh2, Rt2, d2) =>
                   match tryTakeDRK Rh2 Rt2 d2 with
                   | Some (m, Rh3, Rt3, d3) =>
                     if N.eqb a 0 then
                       let Rh4 := pushRunK Sw10 1 Rh3 in
                       let '(Rh5, Rt5) := pushRDK (m + 2) 1 Rh4 Rt3 in
                       Some (mkCfg MJ L Rh5 Rt5 d3)
                     else if N.eqb a 1 then None
                     else
                       Some (mkCfg MR (pushBK (m + 2) (2 * (a - 2)) 1 L) (pushRunK Sw10 1 Rh3) Rt3 d3)
                   | None =>
                     match takeBits2RK false false Rh2 Rt2 d2 with
                     | Some (Rh3, Rt3, d3) =>
                       if N.eqb a 0 then
                         let L' := pushRunK Sw10 1 (pushRunK Sw01 1 (pushRunK (SS 0) 1 L)) in
                         Some (mkCfg MR L' Rh3 Rt3 d3)
                       else None
                     | None =>
                       if N.leb 1 a then
                         let '(ones, Rh3, Rt3, d3) := takeOnesRK Rh2 Rt2 d2 in
                         if N.eqb (N.b2n (N.odd ones)) 1 then
                           match takeBitRK false Rh3 Rt3 d3 with
                           | Some (Rh4, Rt4, d4) =>
                             let mv := N.div2 ones in
                             if N.eqb a 1 then
                               let Rh5 := pushRunK Sb1 1 Rh4 in
                               let '(Rh6, Rt6) := pushRDK (mv + 1) 1 Rh5 Rt4 in
                               let '(Rh7, Rt7) := pushRDK 0 2 Rh6 Rt6 in
                               Some (mkCfg ML L Rh7 Rt7 d4)
                             else
                               Some (mkCfg MR (pushBK (mv + 2) (2 * (a - 2)) 1 L) (pushRunK Sb1 1 Rh4) Rt4 d4)
                           | None => None
                           end
                         else None
                       else None
                     end
                   end
                 end
               end
             else
               match tryTakeDRK Rh1 Rt1 d0 with
               | Some (dn, Rh2, Rt2, d2) =>
                 let kp := N.div2 c10 in
                 let L' := pushRunK Sw10 dn (pushRunK Sw1101 kp (pushRunK (SS 0) 1 L)) in
                 Some (mkCfg MR L' Rh2 Rt2 d2)
               | None =>
                 if N.eqb c10 2 then
                   let '(ones, Rh2, Rt2, d2) := takeOnesRK Rh1 Rt1 d0 in
                   if N.eqb (N.b2n (N.odd ones)) 0 then
                     match takeBits2RK false false Rh2 Rt2 d2 with
                     | Some (Rh3, Rt3, d3) =>
                       let m := N.div2 ones in
                       let L' := pushRunK Sw10 m (pushRunK Sw1101 1 (pushRunK (SS 0) 1 L)) in
                       Some (mkCfg ML L' (pushRunK Sw10 1 Rh3) Rt3 d3)
                     | None => None
                     end
                   else None
                 else None
               end in
         match res10 with
         | Some cfg => Some cfg
         | None =>
           match tryTakeDRK Rh Rt d0 with
           | Some (dn, Rh', Rt', d') => Some (mkCfg MR (pushSK dn 1 L) Rh' Rt' d')
           | None =>
             let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
             let evenRes :=
               if (if N.leb 2 ones then N.eqb (N.b2n (N.odd ones)) 0 else false) then
                 match takeBits2RK false false Rh1 Rt1 d1 with
                 | Some (Rh2, Rt2, d2) =>
                   let Rh3 := pushRunK Sw10 1 Rh2 in
                   let '(Rh4, Rt4) := pushRDK (N.div2 ones) 1 Rh3 Rt2 in
                   Some (mkCfg ML L Rh4 Rt4 d2)
                 | None => None
                 end
               else None in
             match evenRes with
             | Some cfg => Some cfg
             | None =>
               match takeBits3RK true true false Rh Rt d0 with
               | Some (Rh', Rt', d') => Some (mkCfg ML (pushRunK (SS 1) 1 L) (pushRunK Sb1 1 Rh') Rt' d')
               | None => None
               end
             end
           end
         end) = Some cfg' ->
        ValidCfg cfg' /\ CfgR (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg').
      { intro hnd; cbv zeta in hnd.
        pose proof (take10RunsK_spec f64 Rh (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) hRh) as ht10.
        destruct (take10RunsK f64 Rh) as [c10 Rh1a].
        destruct ht10 as [hpRh1a heRh1a].
        split_opt hnd csub hres10.
        - destruct (N.eqb c10 0) eqn:hc10; [discriminate |].
          apply N.eqb_neq in hc10.
          pose proof (normRK_spec Rh1a Rt d0 hpRh1a hRt hD) as hn.
          destruct (normRK Rh1a Rt) as [Rh1 Rt1].
          destruct hn as [p1 [q1 [d1h e1]]].
          assert (hR_c10 : evalR Rh Rt d0 = npow [S1; S0] c10 *> evalR Rh1 Rt1 d0).
          { rewrite e1; unfold evalR; rewrite heRh1a; reflexivity. }
          destruct (N.eqb (N.b2n (N.odd c10)) 1) eqn:hodd.
          + split_opt hres10 csub2 hodd3.
            * destruct (N.eqb c10 3) eqn:hc3; [| discriminate].
              apply N.eqb_eq in hc3; subst c10.
              destruct (tryTakeDRK Rh1 Rt1 d0) as [[[[dn Rh2] Rt2] d2] |] eqn:htd; [| discriminate].
              destruct (tryTakeDRK_spec Rh1 Rt1 Rh2 Rt2 d0 dn d2 p1 q1 d1h htd) as [p2 [q2 [d2h e2]]].
              inversion hodd3; subst.
              split;
                [exact (conj (AllPos_pushRunK Sw11 dn (AllPos_pushRunK Sw1101 2 (AllPos_pushRunK (SS 0) 1 hL)))
                  (conj (AllPos_pushRunK Sb1 1 p2) (conj q2 d2h))) |].
              unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
              rewrite hR_c10, e2, !evalRuns_pushRunK, evalR_pushRunK, !npow_1; unfold evalSym.
              exact (rule_MR_PairedOdd (evalRuns L 0inf) (evalR Rh2 Rt2 d2) dn).
            * set (Rh1' := pushRunK Sw10 (c10 - 1) Rh1) in *.
              destruct (tryTakeDRK Rh1' Rt1 d0) as [[[[a Rh2] Rt2] d2] |] eqn:htd; [| discriminate].
              destruct (tryTakeDRK_spec Rh1' Rt1 Rh2 Rt2 d0 a d2
                (AllPos_pushRunK Sw10 (c10 - 1) p1) q1 d1h htd) as [p2 [q2 [d2h e2]]].
              assert (hR_a : evalR Rh Rt d0 = [S1; S0] *> (D_word a *> evalR Rh2 Rt2 d2)).
              { rewrite hR_c10.
                replace c10 with (1 + (c10 - 1)) at 1 by lia.
                rewrite <- npow_append_npow, npow_1.
                unfold Rh1' in e2; rewrite evalR_pushRunK in e2; unfold evalSym in e2.
                rewrite e2. reflexivity. }
              destruct (tryTakeDRK Rh2 Rt2 d2) as [[[[m Rh3] Rt3] d3] |] eqn:htd2.
              -- destruct (tryTakeDRK_spec Rh2 Rt2 Rh3 Rt3 d2 m d3 p2 q2 d2h htd2) as [p3 [q3 [d3h e3]]].
                 destruct (N.eqb a 0) eqn:ha0.
                 ++ apply N.eqb_eq in ha0; subst a.
                    pose proof (pushRDK_spec (m + 2) 1 (pushRunK Sw10 1 Rh3) Rt3 d3
                      (AllPos_pushRunK Sw10 1 p3) q3 d3h) as hp5.
                    destruct (pushRDK (m + 2) 1 (pushRunK Sw10 1 Rh3) Rt3) as [Rh5 Rt5].
                    inversion hres10; subst.
                    destruct hp5 as [p5 [q5 [d5h e5]]].
                    split; [exact (conj hL (conj p5 (conj q5 d5h))) |].
                    unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                    rewrite hR_a, e3, e5, evalR_pushRunK, !npow_1; unfold evalSym.
                    exact (rule_defect0_D (evalRuns L 0inf) (evalR Rh3 Rt3 d3) m).
                 ++ apply N.eqb_neq in ha0.
                    destruct (N.eqb a 1) eqn:ha1; [discriminate |].
                    apply N.eqb_neq in ha1.
                    inversion hres10; subst.
                    split; [exact (conj (AllPos_pushBK (m + 2) (2 * (a - 2)) 1 hL)
                      (conj (AllPos_pushRunK Sw10 1 p3) (conj q3 d3h))) |].
                    unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                    rewrite hR_a, e3, evalRuns_pushBK, evalR_pushRunK, !npow_1; unfold evalSym.
                    pose proof (rule_defect2_D (evalRuns L 0inf) (evalR Rh3 Rt3 d3) (a - 2) m) as hstep.
                    replace (2 + (a - 2)) with a in hstep by lia.
                    replace (2 + m) with (m + 2) in hstep by lia.
                    exact hstep.
              -- destruct (takeBits2RK false false Rh2 Rt2 d2) as [[[Rh3 Rt3] d3] |] eqn:hb2.
                 ++ destruct (takeBits2RK_spec false false Rh2 Rt2 Rh3 Rt3 d2 d3 p2 q2 d2h hb2)
                      as [p3 [q3 [d3h e3]]].
                    destruct (N.eqb a 0) eqn:ha0; [| discriminate].
                    apply N.eqb_eq in ha0; subst a.
                    inversion hres10; subst.
                    split; [exact (conj (AllPos_pushRunK Sw10 1 (AllPos_pushRunK Sw01 1 (AllPos_pushRunK (SS 0) 1 hL)))
                      (conj p3 (conj q3 d3h))) |].
                    unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                    rewrite hR_a, e3, !evalRuns_pushRunK, !npow_1; unfold evalSym, bitSym.
                    exact (rule_defect_blank0 (evalRuns L 0inf) (evalR Rh3 Rt3 d3)).
                 ++ destruct (N.leb 1 a) eqn:ha1; [| discriminate].
                    apply N.leb_le in ha1.
                    pose proof (takeOnesRK_spec Rh2 Rt2 d2 p2 q2 d2h) as hto.
                    destruct (takeOnesRK Rh2 Rt2 d2) as [[[ones Rh3] Rt3] d3].
                    destruct hto as [p3 [q3 [d3h e3]]].
                    rewrite N_b2n_odd_mod2 in hres10.
                    destruct (N.eqb (ones mod 2) 1) eqn:ho1; [| discriminate].
                    apply N.eqb_eq in ho1.
                    destruct (takeBitRK false Rh3 Rt3 d3) as [[[Rh4 Rt4] d4] |] eqn:hb0; [| discriminate].
                    destruct (takeBitRK_spec false Rh3 Rt3 Rh4 Rt4 d3 d4 p3 q3 d3h hb0)
                      as [p4 [q4 [d4h e4]]].
                    set (mv := N.div2 ones) in *.
                    assert (hones_eq : npow [S1] ones *> ([S0] *> evalR Rh4 Rt4 d4) =
                      [S1] *> (npow [S1; S1] mv *> ([S0] *> evalR Rh4 Rt4 d4))).
                    { unfold mv; rewrite N.div2_div, pow_11_eq_pow_1.
                      replace ones with (1 + (ones / 2) * 2) at 1 by lia.
                      rewrite <- npow_append_npow, npow_1. reflexivity. }
                    destruct (N.eqb a 1) eqn:ha_eq1.
                    ** apply N.eqb_eq in ha_eq1; subst a.
                       pose proof (pushRDK_spec (mv + 1) 1 (pushRunK Sb1 1 Rh4) Rt4 d4
                         (AllPos_pushRunK Sb1 1 p4) q4 d4h) as hp6.
                       destruct (pushRDK (mv + 1) 1 (pushRunK Sb1 1 Rh4) Rt4) as [Rh6 Rt6].
                       destruct hp6 as [p6 [q6 [d6h e6]]].
                       pose proof (pushRDK_spec 0 2 Rh6 Rt6 d4 p6 q6 d6h) as hp7.
                       destruct (pushRDK 0 2 Rh6 Rt6) as [Rh7 Rt7].
                       inversion hres10; subst.
                       destruct hp7 as [p7 [q7 [d7h e7]]].
                       split; [exact (conj hL (conj p7 (conj q7 d7h))) |].
                       unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                       rewrite hR_a, e3, e4; unfold bitSym; change (S0 >> evalR Rh4 Rt4 d4) with ([S0] *> evalR Rh4 Rt4 d4).
                       rewrite hones_eq, e7, e6, evalR_pushRunK, npow_2, !npow_1, Str_app_assoc; unfold evalSym.
                       replace (mv + 1) with (1 + mv) by lia.
                       exact (rule_defect1 (evalRuns L 0inf) (evalR Rh4 Rt4 d4) mv).
                    ** apply N.eqb_neq in ha_eq1.
                       inversion hres10; subst.
                       split; [exact (conj (AllPos_pushBK (mv + 2) (2 * (a - 2)) 1 hL)
                         (conj (AllPos_pushRunK Sb1 1 p4) (conj q4 d4h))) |].
                       unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                       rewrite hR_a, e3, e4; unfold bitSym; change (S0 >> evalR Rh4 Rt4 d4) with ([S0] *> evalR Rh4 Rt4 d4).
                       rewrite hones_eq, evalRuns_pushBK, evalR_pushRunK, !npow_1; unfold evalSym.
                       pose proof (rule_defect2 (evalRuns L 0inf) (evalR Rh4 Rt4 d4) (a - 2) mv) as hstep.
                       replace (2 + (a - 2)) with a in hstep by lia.
                       replace (2 + mv) with (mv + 2) in hstep by lia.
                       exact hstep.
          + rewrite N_b2n_odd_mod2 in hodd.
            assert (hc10_even : c10 mod 2 = 0) by (destruct (N.eqb (c10 mod 2) 1) eqn:heq; [discriminate | apply N.eqb_neq in heq; lia]).
            destruct (tryTakeDRK Rh1 Rt1 d0) as [[[[dn Rh2] Rt2] d2] |] eqn:htd.
            * destruct (tryTakeDRK_spec Rh1 Rt1 Rh2 Rt2 d0 dn d2 p1 q1 d1h htd) as [p2 [q2 [d2h e2]]].
              inversion hres10; subst.
              split; [exact (conj (AllPos_pushRunK Sw10 dn (AllPos_pushRunK Sw1101 (N.div2 c10) (AllPos_pushRunK (SS 0) 1 hL)))
                (conj p2 (conj q2 d2h))) |].
              unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
              rewrite hR_c10, e2, !evalRuns_pushRunK, npow_1, N.div2_div; unfold evalSym.
              replace c10 with ((c10 / 2) * 2) at 1 by lia.
              exact (rule_paired (evalRuns L 0inf) (evalR Rh2 Rt2 d2) (c10 / 2) dn).
            * destruct (N.eqb c10 2) eqn:hc2; [| discriminate].
              apply N.eqb_eq in hc2; subst c10.
              pose proof (takeOnesRK_spec Rh1 Rt1 d0 p1 q1 d1h) as hto.
              destruct (takeOnesRK Rh1 Rt1 d0) as [[[ones Rh2] Rt2] d2].
              destruct hto as [p2 [q2 [d2h e2]]].
              rewrite N_b2n_odd_mod2 in hres10.
              destruct (N.eqb (ones mod 2) 0) eqn:ho0; [| discriminate].
              apply N.eqb_eq in ho0.
              destruct (takeBits2RK false false Rh2 Rt2 d2) as [[[Rh3 Rt3] d3] |] eqn:hb2; [| discriminate].
              destruct (takeBits2RK_spec false false Rh2 Rt2 Rh3 Rt3 d2 d3 p2 q2 d2h hb2)
                as [p3 [q3 [d3h e3]]].
              inversion hres10; subst.
              split; [exact (conj (AllPos_pushRunK Sw10 (N.div2 ones) (AllPos_pushRunK Sw1101 1 (AllPos_pushRunK (SS 0) 1 hL)))
                (conj (AllPos_pushRunK Sw10 1 p3) (conj q3 d3h))) |].
              unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
              rewrite hR_c10, e2, e3, !evalRuns_pushRunK, evalR_pushRunK, npow_2, !npow_1, N.div2_div;
                unfold evalSym, bitSym.
              replace ones with ((ones / 2) * 2) at 1 by lia.
              rewrite <- pow_11_eq_pow_1.
              exact (rule_MR_PairedEven (evalRuns L 0inf) (evalR Rh3 Rt3 d3) (ones / 2)).
        - destruct (tryTakeDRK Rh Rt d0) as [[[[dn Rh'] Rt'] d'] |] eqn:htd.
          + destruct (tryTakeDRK_spec Rh Rt Rh' Rt' d0 dn d' hRh hRt hD htd) as [p1 [q1 [d1h e1]]].
            inversion hnd; subst.
            split; [exact (conj (AllPos_pushSK dn 1 hL) (conj p1 (conj q1 d1h))) |].
            unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
            rewrite e1, evalRuns_pushSK, npow_1.
            exact (rule_right (evalRuns L 0inf) (evalR Rh' Rt' d') dn).
          + pose proof (takeOnesRK_spec Rh Rt d0 hRh hRt hD) as hto.
            destruct (takeOnesRK Rh Rt d0) as [[[ones Rh1] Rt1] d1].
            destruct hto as [p1 [q1 [d1h e1]]].
            split_opt hnd csub2 heven.
            * destruct (N.leb 2 ones) eqn:ho2; [| discriminate].
              apply N.leb_le in ho2.
              rewrite N_b2n_odd_mod2 in heven.
              destruct (N.eqb (ones mod 2) 0) eqn:ho0; [| discriminate].
              apply N.eqb_eq in ho0.
              destruct (takeBits2RK false false Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:hb2; [| discriminate].
              destruct (takeBits2RK_spec false false Rh1 Rt1 Rh2 Rt2 d1 d2 p1 q1 d1h hb2)
                as [p2 [q2 [d2h e2]]].
              pose proof (pushRDK_spec (N.div2 ones) 1 (pushRunK Sw10 1 Rh2) Rt2 d2
                (AllPos_pushRunK Sw10 1 p2) q2 d2h) as hp4.
              destruct (pushRDK (N.div2 ones) 1 (pushRunK Sw10 1 Rh2) Rt2) as [Rh4 Rt4].
              inversion heven; subst.
              destruct hp4 as [p4 [q4 [d4h e4]]].
              split; [exact (conj hL (conj p4 (conj q4 d4h))) |].
              unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
              rewrite e1, e2, e4, evalR_pushRunK, !npow_1, N.div2_div; unfold evalSym, bitSym.
              set (n0 := ones / 2 - 1).
              replace ones with ((1 + n0) * 2) by (unfold n0; lia).
              replace ((1 + n0) * 2 / 2) with (1 + n0) by lia.
              rewrite <- pow_11_eq_pow_1.
              exact (rule_even (evalRuns L 0inf) (evalR Rh2 Rt2 d2) n0).
            * destruct (takeBits3RK true true false Rh Rt d0) as [[[Rh' Rt'] d'] |] eqn:hb3; [| discriminate].
              destruct (takeBits3RK_spec true true false Rh Rt Rh' Rt' d0 d' hRh hRt hD hb3)
                as [p' [q' [d'h e']]].
              inversion hnd; subst.
              split; [exact (conj (AllPos_pushRunK (SS 1) 1 hL) (conj (AllPos_pushRunK Sb1 1 p') (conj q' d'h))) |].
              unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
              rewrite e', evalRuns_pushRunK, evalR_pushRunK, !npow_1; unfold evalSym, bitSym.
              exact (rule_MR_110 (evalRuns L 0inf) (evalR Rh' Rt' d')). }
      destruct rw; try exact (hnonD h).
      (* rw = SD n *)
      split_opt h csub hcall.
      * assert (hcall_gen :
          (let '(b1, L1) := take10RunsK f64 L in
           if N.eqb b1 0 then None
           else
             let '(c111, L2) := take111RunsK L1 in
             let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 (c111 + 1) true in
             if N.eqb hd 0 then None
             else
               let rem := c111 - (hd - 1) in
               Some (mkCfg ML (pushRunK Sw10 b1 (pushRunK Sw111 rem L2)) nRh nRt nD0)) = Some cfg' ->
          ValidCfg cfg' /\ CfgR (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg').
        { intro hcg.
          pose proof (take10RunsK_spec f64 L 0inf hL) as ht10.
          destruct (take10RunsK f64 L) as [b1 L1].
          destruct ht10 as [hpL1 heL1].
          destruct (N.eqb b1 0) eqn:hb1; [discriminate |].
          apply N.eqb_neq in hb1.
          pose proof (take111RunsK_spec L1 0inf hpL1) as ht111.
          destruct (take111RunsK L1) as [c111 L2].
          destruct ht111 as [hpL2 heL2].
          pose proof (doCallsNoneK_sound Rh Rt d0 (c111 + 1) true ltac:(lia) hRh hRt hD) as hdc.
          destruct (doCallsNoneK Rh Rt d0 (c111 + 1) true) as [[[hd nRh] nRt] nD0].
          destruct hdc as [pnRh [pnRt [dnRt [hhd hnc]]]].
          destruct (N.eqb hd 0) eqn:hhd0; [discriminate |].
          apply N.eqb_neq in hhd0.
          inversion hcg; subst.
          split; [exact (conj (AllPos_pushRunK Sw10 b1 (AllPos_pushRunK Sw111 (c111 - (hd - 1)) hpL2))
            (conj pnRh (conj pnRt dnRt))) |].
          unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
          rewrite heL1, heL2, !evalRuns_pushRunK; unfold evalSym.
          replace c111 with ((hd - 1) + (c111 - (hd - 1))) at 1 by lia.
          rewrite <- npow_append_npow.
          replace hd with ((hd - 1) + 1) in hnc by lia.
          pose proof (NCalls_from_MR (hd - 1) (b1 - 1)
            (npow [S1; S1; S1] (c111 - (hd - 1)) *> evalRuns L2 0inf)
            (evalR Rh Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
          replace (1 + (b1 - 1)) with b1 in hstep by lia.
          exact hstep. }
        destruct L as [| [lw lk] L']; [exact (hcall_gen hcall) |].
        destruct lw as [| | ba bc | | | | | | | |]; try exact (hcall_gen hcall).
        destruct (N.leb 1 ba) eqn:hba; [| discriminate].
        apply N.leb_le in hba.
        set (c111av := bc / 3 + (if N.eqb (bc mod 3) 2 then 1 else 0)) in *.
        pose proof (doCallsNoneK_sound Rh Rt d0 (c111av + 1) true ltac:(lia) hRh hRt hD) as hdc.
        destruct (doCallsNoneK Rh Rt d0 (c111av + 1) true) as [[[hd nRh] nRt] nD0].
        destruct hdc as [pnRh [pnRt [dnRt [hhd hnc]]]].
        destruct (N.eqb hd 0) eqn:hhd0; [discriminate |].
        apply N.eqb_neq in hhd0.
        set (used := hd - 1) in *.
        set (L1 := decRunK (SB ba bc) lk L') in *.
        pose proof (evalRuns_decRunK (SB ba bc) lk L' 0inf (proj1 hL)) as hdec.
        pose proof (AllPos_decRunK (SB ba bc) lk (proj2 hL)) as hpL1.
        destruct (N.leb (3 * used) bc) eqn:h3u.
        -- apply N.leb_le in h3u.
           inversion hcall; subst.
           split; [exact (conj (AllPos_pushBK ba (bc - 3 * used) 1 hpL1) (conj pnRh (conj pnRt dnRt))) |].
           unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
           rewrite <- hdec, evalRuns_pushBK, npow_1; unfold evalSym.
           replace hd with (used + 1) in hnc by lia.
           pose proof (B_word_MR_calls_le (ba - 1) bc used h3u (evalRuns L1 0inf)
             (evalR Rh Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
           replace (1 + (ba - 1)) with ba in hstep by lia.
           exact hstep.
        -- apply N.leb_gt in h3u.
           assert (hbc_mod : bc mod 3 = 2 /\ used = bc / 3 + 1).
           { unfold c111av, used in *.
             destruct (N.eqb (bc mod 3) 2) eqn:hm2;
               [apply N.eqb_eq in hm2 | apply N.eqb_neq in hm2]; lia. }
           destruct hbc_mod as [hbc2 hused].
           inversion hcall; subst.
           split; [exact (conj (AllPos_pushRunK Sw10 ba (AllPos_pushRunK Sw01 1 (AllPos_pushRunK (SS 0) 1 hpL1)))
             (conj pnRh (conj pnRt dnRt))) |].
           unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
           rewrite <- hdec, !evalRuns_pushRunK, !npow_1; unfold evalSym.
           replace hd with ((bc / 3) + 2) in hnc by lia.
           pose proof (B_word_MR_calls_gt (ba - 1) (bc / 3) (evalRuns L1 0inf)
             (evalR Rh Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
           replace (1 + (ba - 1)) with ba in hstep by lia.
           replace (3 * (bc / 3) + 2) with bc in hstep by lia.
           exact hstep.
      * pose proof (sweepDK_spec L Rh (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) hL hRh) as hsw.
        destruct (sweepDK L Rh) as [L' Rh'].
        inversion h; subst.
        destruct hsw as [pL' [pRh' hstep]].
        exact (conj (conj pL' (conj pRh' (conj hRt hD))) hstep).
Qed.

Lemma stepMLK_sound (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) (cfg' : FastCfg)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : stepMLK f64 f4096 L Rh Rt d0 = Some cfg') :
  ValidCfg cfg' /\ CfgL (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg'.
Proof.
  unfold stepMLK in h.
  split_opt h csub hdtail.
  - destruct Rh; [| discriminate].
    exact (runDtailLoopK_sound f4096 ML L Rt d0 cfg' hL hRt hD hdtail).
  - assert (hrestL :
      (let '(b1, L1) := take10RunsK f64 L in
       let res10 :=
         if N.eqb b1 0 then None
         else
           let '(c111, L2) := take111RunsK L1 in
           if N.eqb c111 0 then
             match takeBits5RunsK false true true false true L2 with
             | Some L3 =>
               let '(Rh1, Rt1) := pushRDK b1 1 Rh Rt in
               Some (mkCfg MJ L3 Rh1 Rt1 d0)
             | None =>
               let over2 :=
                 match takeBits2RunsK true true L2 with
                 | Some L3 =>
                   if isAllZeroRunsK L3 then
                     Some (mkCfg MR (pushRunK Sw10 2 (pushRunK Sw11 b1 [])) (pushRunK Sb1 1 Rh) Rt d0)
                   else None
                 | None => None
                 end in
               match over2 with
               | Some cfg => Some cfg
               | None =>
                 match takeBitRunsK true L2 with
                 | Some L3 =>
                   if isAllZeroRunsK L3 then
                     match tryTakeDRK Rh Rt d0 with
                     | Some (dn, Rh', Rt', d') =>
                       Some (mkCfg MR (pushRunK Sw10 (dn + 2) (pushRunK Sw11 (b1 - 1) [])) (pushRunK Sw10 1 Rh') Rt' d')
                     | None => None
                     end
                   else None
                 | None => None
                 end
               end
             end
           else
             match Rh with
             | [] => Some (mkCfg ML (pushRunK Sw10 b1 L2) [] Rt (d0 + 2 * c111))
             | _ :: _ =>
               let '(hd, nRh, nRt, nD0) := doCallsNoneK Rh Rt d0 c111 true in
               if N.eqb hd 0 then
                 Some (mkCfg MR (pushRunK Sw10 b1 (pushRunK Sw111 (c111 - 1) L2)) Rh Rt d0)
               else
                 Some (mkCfg ML (pushRunK Sw10 b1 (pushRunK Sw111 (c111 - hd) L2)) nRh nRt nD0)
             end in
       match res10 with
       | Some cfg => Some cfg
       | None =>
         match tryTakeSK f64 L with
         | Some (sn, L') =>
           let '(Rh1, Rt1) := pushRDK sn 1 Rh Rt in
           Some (mkCfg ML L' Rh1 Rt1 d0)
         | None =>
           let turnB :=
             match takeBits2RunsK true true L with
             | Some L' =>
               match tryTakeDRK Rh Rt d0 with
               | Some (dn, Rh', Rt', d') => Some (mkCfg MR (pushRunK Sw10 (dn + 1) L') Rh' Rt' d')
               | None =>
                 let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
                 if N.eqb (N.b2n (N.odd ones)) 0 then
                   match takeBitRK false Rh1 Rt1 d1 with
                   | Some (Rh2, Rt2, d2) =>
                     Some (mkCfg ML (pushRunK Sw10 (N.div2 ones + 1) L') (pushRunK Sb1 1 Rh2) Rt2 d2)
                   | None => None
                   end
                 else None
               end
             | None => None
             end in
           match turnB with
           | Some cfg => Some cfg
           | None =>
             let '(k01, L') := take01RunsK f64 L in
             if N.eqb k01 0 then
               match takeBits2RunsK true false L with
               | Some L' => Some (mkCfg MJ L' Rh Rt d0)
               | None =>
                 if isAllZeroRunsK L then
                   let '(ones, Rh1, Rt1, d1) := takeOnesRK Rh Rt d0 in
                   match takeBits2RK false false Rh1 Rt1 d1 with
                   | Some (Rh2, Rt2, d2) =>
                     Some (mkCfg ML (pushRunK Sb1 (ones + 4) []) (pushRunK Sb1 1 Rh2) Rt2 d2)
                   | None => None
                   end
                 else None
               end
             else
               match Rh with
               | mkRun (SD dn) kd :: Rh' =>
                 let '(Rh1, Rt1) := pushRDK (dn + k01) 1 (decRunK (SD dn) kd Rh') Rt in
                 Some (mkCfg ML L' Rh1 Rt1 d0)
               | [] =>
                 match Rt with
                 | mkRun (SD dn) kd :: Rt' =>
                   Some (mkCfg ML L' [] (pushDK (dn + k01) 1 (decRunK (SD dn) kd Rt')) d0)
                 | [] =>
                   if N.eqb d0 0 then Some (mkCfg ML L' (pushRunK Sw11 k01 []) [] 0)
                   else Some (mkCfg ML L' [] [mkRun (SD k01) 1] (d0 - 1))
                 | _ => Some (mkCfg ML L' (pushRunK Sw11 k01 []) Rt d0)
                 end
               | _ => Some (mkCfg ML L' (pushRunK Sw11 k01 Rh) Rt d0)
               end
           end
         end
       end) = Some cfg' ->
      ValidCfg cfg' /\ CfgL (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg').
    { intro hrl; cbv zeta in hrl.
      pose proof (take10RunsK_spec f64 L 0inf hL) as ht10.
      destruct (take10RunsK f64 L) as [b1 L1].
      destruct ht10 as [hpL1 heL1].
      split_opt hrl csub hres10.
      - destruct (N.eqb b1 0) eqn:hb1; [discriminate |].
        apply N.eqb_neq in hb1.
        pose proof (take111RunsK_spec L1 0inf hpL1) as ht111.
        destruct (take111RunsK L1) as [c111 L2].
        destruct ht111 as [hpL2 heL2].
        destruct (N.eqb c111 0) eqn:hc111.
        + apply N.eqb_eq in hc111; subst c111.
          rewrite npow_0 in heL2; cbn [Str_app] in heL2.
          destruct (takeBits5RunsK false true true false true L2) as [L3 |] eqn:hb5.
          * destruct (takeBits5RunsK_spec false true true false true L2 L3 hpL2 hb5) as [hpL3 heL3].
            pose proof (pushRDK_spec b1 1 Rh Rt d0 hRh hRt hD) as hp1.
            destruct (pushRDK b1 1 Rh Rt) as [Rh1 Rt1].
            inversion hres10; subst.
            destruct hp1 as [p1 [q1 [d1h e1]]].
            split; [exact (conj hpL3 (conj p1 (conj q1 d1h))) |].
            unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
            rewrite heL1, heL2, heL3, e1, npow_1; unfold bitSym.
            change ([S0; S1; S1; S0; S1] *> evalRuns L3 0inf)
              with ([S0; S1] *> (S_word 0 *> evalRuns L3 0inf)).
            pose proof (rule_finishP (evalRuns L3 0inf) (evalR Rh Rt d0) (b1 - 1)) as hstep.
            replace (1 + (b1 - 1)) with b1 in hstep by lia.
            exact hstep.
          * split_opt hres10 csub2 hover2.
            -- destruct (takeBits2RunsK true true L2) as [L3 |] eqn:hb2; [| discriminate].
               destruct (takeBits2RunsK_spec true true L2 L3 hpL2 hb2) as [_ heL3].
               destruct (isAllZeroRunsK L3) eqn:hz; [| discriminate].
               inversion hover2; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 2 (AllPos_pushRunK Sw11 b1 (I : AllPos [])))
                 (conj (AllPos_pushRunK Sb1 1 hRh) (conj hRt hD))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL1, heL2, heL3, (isAllZeroRunsK_spec hz), !evalRuns_pushRunK, evalR_pushRunK, npow_1;
                 cbn [evalRuns]; unfold evalSym, bitSym.
               pose proof (rule_overflow2 (evalR Rh Rt d0) (b1 - 1)) as hstep.
               replace (1 + (b1 - 1)) with b1 in hstep by lia.
               exact hstep.
            -- destruct (takeBitRunsK true L2) as [L3 |] eqn:hb1t; [| discriminate].
               destruct (takeBitRunsK_spec true L2 L3 hpL2 hb1t) as [_ heL3].
               destruct (isAllZeroRunsK L3) eqn:hz; [| discriminate].
               destruct (tryTakeDRK Rh Rt d0) as [[[[dn Rh'] Rt'] d'] |] eqn:htd; [| discriminate].
               destruct (tryTakeDRK_spec Rh Rt Rh' Rt' d0 dn d' hRh hRt hD htd) as [p' [q' [d'h e']]].
               inversion hres10; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 (dn + 2) (AllPos_pushRunK Sw11 (b1 - 1) (I : AllPos [])))
                 (conj (AllPos_pushRunK Sw10 1 p') (conj q' d'h))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL1, heL2, heL3, (isAllZeroRunsK_spec hz), e', !evalRuns_pushRunK, evalR_pushRunK, npow_1;
                 cbn [evalRuns]; unfold evalSym, bitSym.
               pose proof (rule_overflow1 (evalR Rh' Rt' d') (b1 - 1) dn) as hstep.
               replace (1 + (b1 - 1)) with b1 in hstep by lia.
               exact hstep.
        + apply N.eqb_neq in hc111.
          destruct Rh as [| r0 rrest].
          * inversion hres10; subst.
            split; [exact (conj (AllPos_pushRunK Sw10 b1 hpL2) (conj I (conj hRt hD))) |].
            unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
            rewrite heL1, heL2, evalRuns_pushRunK; unfold evalSym.
            pose proof (NCalls_pureD_tail Rt hD c111 d0) as hc.
            pose proof (NCalls_from_ML c111 (b1 - 1) (evalRuns L2 0inf)
              (evalR [] Rt d0) (evalR [] Rt (d0 + 2 * c111)) hc) as hstep.
            replace (1 + (b1 - 1)) with b1 in hstep by lia.
            exact hstep.
          * pose proof (doCallsNoneK_sound (r0 :: rrest) Rt d0 c111 true ltac:(lia) hRh hRt hD) as hdc.
            destruct (doCallsNoneK (r0 :: rrest) Rt d0 c111 true) as [[[hd nRh] nRt] nD0].
            destruct hdc as [pnRh [pnRt [dnRt [hhd hnc]]]].
            destruct (N.eqb hd 0) eqn:hhd0.
            -- inversion hres10; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 b1 (AllPos_pushRunK Sw111 (c111 - 1) hpL2))
                 (conj hRh (conj hRt hD))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL1, heL2, !evalRuns_pushRunK; unfold evalSym.
               replace c111 with (1 + (c111 - 1)) at 1 by lia.
               rewrite <- npow_append_npow, npow_1.
               pose proof (rule_restart (npow [S1; S1; S1] (c111 - 1) *> evalRuns L2 0inf)
                 (evalR (r0 :: rrest) Rt d0) (b1 - 1)) as hstep.
               replace (1 + (b1 - 1)) with b1 in hstep by lia.
               exact hstep.
            -- inversion hres10; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 b1 (AllPos_pushRunK Sw111 (c111 - hd) hpL2))
                 (conj pnRh (conj pnRt dnRt))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL1, heL2, !evalRuns_pushRunK; unfold evalSym.
               replace c111 with (hd + (c111 - hd)) at 1 by lia.
               rewrite <- npow_append_npow.
               pose proof (NCalls_from_ML hd (b1 - 1) (npow [S1; S1; S1] (c111 - hd) *> evalRuns L2 0inf)
                 (evalR (r0 :: rrest) Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
               replace (1 + (b1 - 1)) with b1 in hstep by lia.
               exact hstep.
      - destruct (tryTakeSK f64 L) as [[sn L'] |] eqn:hts.
        + destruct (tryTakeSK_spec f64 L L' sn hL hts) as [hpL' heL'].
          pose proof (pushRDK_spec sn 1 Rh Rt d0 hRh hRt hD) as hp1.
          destruct (pushRDK sn 1 Rh Rt) as [Rh1 Rt1].
          inversion hrl; subst.
          destruct hp1 as [p1 [q1 [d1h e1]]].
          split; [exact (conj hpL' (conj p1 (conj q1 d1h))) |].
          unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
          rewrite heL', e1, npow_1.
          exact (rule_left (evalRuns L' 0inf) (evalR Rh Rt d0) sn).
        + split_opt hrl csub2 hturnB.
          * destruct (takeBits2RunsK true true L) as [L' |] eqn:hb2; [| discriminate].
            destruct (takeBits2RunsK_spec true true L L' hL hb2) as [hpL' heL'].
            destruct (tryTakeDRK Rh Rt d0) as [[[[dn Rh'] Rt'] d'] |] eqn:htd.
            -- destruct (tryTakeDRK_spec Rh Rt Rh' Rt' d0 dn d' hRh hRt hD htd) as [p' [q' [d'h e']]].
               inversion hturnB; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 (dn + 1) hpL') (conj p' (conj q' d'h))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL', e', evalRuns_pushRunK; unfold evalSym, bitSym.
               replace (dn + 1) with (1 + dn) by lia.
               exact (rule_turnB (evalRuns L' 0inf) (evalR Rh' Rt' d') dn).
            -- pose proof (takeOnesRK_spec Rh Rt d0 hRh hRt hD) as hto.
               destruct (takeOnesRK Rh Rt d0) as [[[ones Rh1] Rt1] d1].
               destruct hto as [p1 [q1 [d1h e1]]].
               rewrite N_b2n_odd_mod2 in hturnB.
               destruct (N.eqb (ones mod 2) 0) eqn:ho0; [| discriminate].
               apply N.eqb_eq in ho0.
               destruct (takeBitRK false Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:hb0; [| discriminate].
               destruct (takeBitRK_spec false Rh1 Rt1 Rh2 Rt2 d1 d2 p1 q1 d1h hb0)
                 as [p2 [q2 [d2h e2]]].
               inversion hturnB; subst.
               split; [exact (conj (AllPos_pushRunK Sw10 (N.div2 ones + 1) hpL')
                 (conj (AllPos_pushRunK Sb1 1 p2) (conj q2 d2h))) |].
               unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
               rewrite heL', e1, e2, evalRuns_pushRunK, evalR_pushRunK, npow_1, N.div2_div;
                 unfold evalSym, bitSym.
               replace ones with ((ones / 2) * 2) at 1 by lia.
               rewrite <- pow_11_eq_pow_1.
               exact (rule_ML_TurnB_even (evalRuns L' 0inf) (evalR Rh2 Rt2 d2) (ones / 2)).
          * pose proof (take01RunsK_spec f64 L hL) as ht01.
            destruct (take01RunsK f64 L) as [k01 L'].
            destruct ht01 as [hpL' heL'].
            destruct (N.eqb k01 0) eqn:hk01.
            -- destruct (takeBits2RunsK true false L) as [L2' |] eqn:hb2.
               ++ destruct (takeBits2RunsK_spec true false L L2' hL hb2) as [hpL2' heL2'].
                  inversion hrl; subst.
                  split; [exact (conj hpL2' (conj hRh (conj hRt hD))) |].
                  unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                  rewrite heL2'; unfold bitSym.
                  exact (rule_ML_10 (evalRuns L2' 0inf) (evalR Rh Rt d0)).
               ++ destruct (isAllZeroRunsK L) eqn:hz; [| discriminate].
                  pose proof (takeOnesRK_spec Rh Rt d0 hRh hRt hD) as hto.
                  destruct (takeOnesRK Rh Rt d0) as [[[ones Rh1] Rt1] d1].
                  destruct hto as [p1 [q1 [d1h e1]]].
                  destruct (takeBits2RK false false Rh1 Rt1 d1) as [[[Rh2 Rt2] d2] |] eqn:hb00; [| discriminate].
                  destruct (takeBits2RK_spec false false Rh1 Rt1 Rh2 Rt2 d1 d2 p1 q1 d1h hb00)
                    as [p2 [q2 [d2h e2]]].
                  inversion hrl; subst.
                  split; [exact (conj (AllPos_pushRunK Sb1 (ones + 4) (I : AllPos []))
                    (conj (AllPos_pushRunK Sb1 1 p2) (conj q2 d2h))) |].
                  unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                  rewrite (isAllZeroRunsK_spec hz), e1, e2, evalRuns_pushRunK, evalR_pushRunK, npow_1;
                    cbn [evalRuns]; unfold evalSym, bitSym.
                  exact (rule_ML_default (evalR Rh2 Rt2 d2) ones).
            -- apply N.eqb_neq in hk01.
               assert (h01_step : CfgL (evalRuns L 0inf) (evalR Rh Rt d0) -->*
                 CfgL (evalRuns L' 0inf) (npow [S1; S1] k01 *> evalR Rh Rt d0)).
               { rewrite heL'. exact (rule_ML_01 (evalRuns L' 0inf) (evalR Rh Rt d0) k01). }
               destruct Rh as [| [rw rk] rrest].
               ++ destruct Rt as [| [tw tk] trest].
                  ** destruct (N.eqb d0 0) eqn:hd0.
                     --- apply N.eqb_eq in hd0; subst d0.
                         inversion hrl; subst.
                         split; [exact (conj hpL' (conj (AllPos_pushRunK Sw11 k01 (I : AllPos [])) (conj I I))) |].
                         unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                         rewrite evalR_pushRunK; unfold evalSym; exact h01_step.
                     --- apply N.eqb_neq in hd0.
                         inversion hrl; subst.
                         split; [exact (conj hpL' (conj I (conj (conj (N.le_refl 1) I) I))) |].
                         unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                         assert (hrhs : npow [S1; S1] k01 *> evalR [] [] d0 =
                           evalR [] [mkRun (SD k01) 1] (d0 - 1)).
                         { unfold evalR; cbn [evalRuns evalSym].
                           rewrite npow_1.
                           replace d0 with (1 + (d0 - 1)) at 1 by lia.
                           rewrite <- npow_append_npow, npow_1, w11_absorb_D_word, N.add_0_l.
                           reflexivity. }
                         rewrite hrhs in h01_step. exact h01_step.
                  ** destruct tw; try contradiction.
                     inversion hrl; subst.
                     split; [exact (conj hpL' (conj I (conj (AllPos_pushDK (n + k01) 1 (AllPos_decRunK (SD n) tk (proj2 hRt)))
                       (AllD_pushDK (n + k01) 1 (AllD_decRunK n tk hD))))) |].
                     unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                     assert (hrhs : npow [S1; S1] k01 *> evalR [] (mkRun (SD n) tk :: trest) d0 =
                       evalR [] (pushDK (n + k01) 1 (decRunK (SD n) tk trest)) d0).
                     { rewrite evalR_nil_pushDK, npow_1.
                       pose proof (evalRuns_decRunK (SD n) tk trest (npow (D_word 0) d0 *> 0inf) (proj1 hRt)) as hdec.
                       unfold evalR; cbn [evalRuns].
                       rewrite <- hdec; unfold evalSym.
                       exact (w11_absorb_D_word k01 n _). }
                     rewrite hrhs in h01_step. exact h01_step.
               ++ destruct rw;
                    try (inversion hrl; subst;
                         split; [exact (conj hpL' (conj (AllPos_pushRunK Sw11 k01 hRh) (conj hRt hD))) |];
                         unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0];
                         rewrite evalR_pushRunK; unfold evalSym; exact h01_step).
                  pose proof (pushRDK_spec (n + k01) 1 (decRunK (SD n) rk rrest) Rt d0
                    (AllPos_decRunK (SD n) rk (proj2 hRh)) hRt hD) as hp1.
                  destruct (pushRDK (n + k01) 1 (decRunK (SD n) rk rrest) Rt) as [Rh1 Rt1].
                  inversion hrl; subst.
                  destruct hp1 as [p1 [q1 [d1h e1]]].
                  split; [exact (conj hpL' (conj p1 (conj q1 d1h))) |].
                  unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
                  assert (hrhs : npow [S1; S1] k01 *> evalR (mkRun (SD n) rk :: rrest) Rt d0 =
                    evalR Rh1 Rt1 d0).
                  { rewrite e1, npow_1.
                    pose proof (evalRuns_decRunK (SD n) rk rrest (evalRuns Rt (npow (D_word 0) d0 *> 0inf)) (proj1 hRh)) as hdec.
                    unfold evalR; cbn [evalRuns].
                    rewrite <- hdec; unfold evalSym.
                    exact (w11_absorb_D_word k01 n _). }
                  rewrite hrhs in h01_step. exact h01_step. }
    destruct L as [| [lw lk] L']; [exact (hrestL h) |].
    destruct lw as [| sn | ba bc | | | | | | | |]; try exact (hrestL h).
    + (* lw = SS sn *)
      pose proof (sweepSK_spec (mkRun (SS sn) lk :: L') Rh Rt d0 hL hRh hRt hD) as hsw.
      destruct (sweepSK (mkRun (SS sn) lk :: L') Rh Rt) as [[L1' Rh1'] Rt1'].
      inversion h; subst.
      destruct hsw as [pL [pRh [pRt [dRt hstep]]]].
      exact (conj (conj pL (conj pRh (conj pRt dRt))) hstep).
    + (* lw = SB ba bc *)
      split_opt h csub hcoll.
      * destruct Rh as [| r0 rrest]; [discriminate |].
        destruct (if N.eqb (bc mod 3) 2 then N.leb 1 ba else false) eqn:hcond; [| discriminate].
        destruct (N.eqb (bc mod 3) 2) eqn:hbc2; [| discriminate].
        apply N.eqb_eq in hbc2; apply N.leb_le in hcond.
        set (stepH := bc / 3 + 1) in *.
        set (av := N.div2 (peekCollZAvailK (r0 :: rrest) Rt d0) / stepH) in *.
        set (mc := if N.leb lk av then lk else av) in *.
        destruct (N.eqb mc 0) eqn:hmc0; [discriminate |].
        apply N.eqb_neq in hmc0.
        assert (hmc_le : 1 <= mc /\ mc <= lk).
        { unfold mc; destruct (N.leb lk av) eqn:hlk;
            [apply N.leb_le in hlk | apply N.leb_gt in hlk]; lia. }
        destruct hmc_le as [hmc1 hmc_lk].
        set (need := mc * stepH) in *.
        assert (hneed1 : 1 <= need) by (unfold need, stepH; nia).
        pose proof (doCallsNoneK_sound (r0 :: rrest) Rt d0 need false hneed1 hRh hRt hD) as hdc.
        destruct (doCallsNoneK (r0 :: rrest) Rt d0 need false) as [[[hd nRh] nRt] nD0].
        destruct hdc as [pnRh [pnRt [dnRt [_ hnc]]]].
        destruct (N.eqb hd need) eqn:hhd; [| discriminate].
        apply N.eqb_eq in hhd; subst hd.
        set (L1 := if N.eqb lk mc then L' else mkRun (SB ba bc) (lk - mc) :: L') in *.
        assert (hL1 : AllPos L1 /\
          evalRuns (mkRun (SB ba bc) lk :: L') 0inf = npow (B_word ba bc) mc *> evalRuns L1 0inf).
        { unfold L1. destruct (N.eqb lk mc) eqn:hlkmc.
          - apply N.eqb_eq in hlkmc; rewrite hlkmc. exact (conj (proj2 hL) eq_refl).
          - apply N.eqb_neq in hlkmc.
            split; [simpl; split; [lia | exact (proj2 hL)] |].
            cbn [evalRuns]; unfold evalSym.
            replace lk with (mc + (lk - mc)) at 1 by lia.
            rewrite <- npow_append_npow. reflexivity. }
        destruct hL1 as [hpL1 heL1].
        pose proof (pushRDK_spec ba 1 nRh nRt nD0 pnRh pnRt dnRt) as hp1.
        destruct (pushRDK ba 1 nRh nRt) as [nRh1 nRt1].
        destruct hp1 as [p1 [q1 [d1h e1]]].
        pose proof (pushRDK_spec (ba + 1) (mc - 1) nRh1 nRt1 nD0 p1 q1 d1h) as hp2.
        destruct (pushRDK (ba + 1) (mc - 1) nRh1 nRt1) as [nRh2 nRt2].
        inversion hcoll; subst.
        destruct hp2 as [p2 [q2 [d2h e2]]].
        split; [exact (conj hpL1 (conj p2 (conj q2 d2h))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
        rewrite heL1, e2, e1, npow_1.
        unfold need, stepH in hnc.
        replace mc with (1 + (mc - 1)) in hnc by lia.
        pose proof (B_word_ML_r2_pow (ba - 1) (bc / 3) (mc - 1) (evalRuns L1 0inf)
          (evalR (r0 :: rrest) Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
        replace (1 + (ba - 1)) with ba in hstep by lia.
        replace (2 + (ba - 1)) with (ba + 1) in hstep by lia.
        replace (3 * (bc / 3) + 2) with bc in hstep by lia.
        replace (1 + (mc - 1)) with mc in hstep by lia.
        exact hstep.
      * inversion h; subst.
        set (L1 := decRunK (SB ba bc) lk L').
        pose proof (AllPos_decRunK (SB ba bc) lk (proj2 hL)) as hpL1.
        split;
          [exact (conj (AllPos_pushRunK Sw10 ba (AllPos_pushRunK Sb1 bc (AllPos_pushRunK (SS 0) 2 hpL1)))
            (conj hRh (conj hRt hD))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
        pose proof (evalRuns_decRunK (SB ba bc) lk L' 0inf (proj1 hL)) as hdec.
        rewrite <- hdec, evalRuns_B_unpack; unfold evalSym.
        exact (evstep_refl tm _).
Qed.

Lemma stepMJK_sound (f64 f4096 : nat) (L Rh Rt : Runs) (d0 : N) (cfg' : FastCfg)
  (hL : AllPos L) (hRh : AllPos Rh) (hRt : AllPos Rt) (hD : AllD Rt)
  (h : stepMJK f64 f4096 L Rh Rt d0 = Some cfg') :
  ValidCfg cfg' /\ CfgJ (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg'.
Proof.
  unfold stepMJK in h.
  split_opt h csub hdtail.
  - destruct Rh; [| discriminate].
    exact (runDtailLoopK_sound f4096 MJ L Rt d0 cfg' hL hRt hD hdtail).
  - assert (hrestL :
      (match tryTakeSK f64 L with
       | Some (sn, L') =>
         let '(Rh1, Rt1) := pushRDK (sn + 1) 1 Rh Rt in
         Some (mkCfg ML L' Rh1 Rt1 d0)
       | None =>
         if isAllZeroRunsK L then
           Some (mkCfg ML (pushRunK Sw111 1 []) (pushRunK Sb1 1 Rh) Rt d0)
         else None
       end) = Some cfg' ->
      ValidCfg cfg' /\ CfgJ (evalRuns L 0inf) (evalR Rh Rt d0) -->* evalCfg cfg').
    { intro hrl.
      destruct (tryTakeSK f64 L) as [[sn L'] |] eqn:hts.
      - destruct (tryTakeSK_spec f64 L L' sn hL hts) as [hpL' heL'].
        pose proof (pushRDK_spec (sn + 1) 1 Rh Rt d0 hRh hRt hD) as hp1.
        destruct (pushRDK (sn + 1) 1 Rh Rt) as [Rh1 Rt1].
        inversion hrl; subst.
        destruct hp1 as [p1 [q1 [d1h e1]]].
        split; [exact (conj hpL' (conj p1 (conj q1 d1h))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
        rewrite heL', e1, npow_1.
        replace (sn + 1) with (1 + sn) by lia.
        exact (rule_leftJ (evalRuns L' 0inf) (evalR Rh Rt d0) sn).
      - destruct (isAllZeroRunsK L) eqn:hz; [| discriminate].
        inversion hrl; subst.
        split; [exact (conj (AllPos_pushRunK Sw111 1 (I : AllPos []))
          (conj (AllPos_pushRunK Sb1 1 hRh) (conj hRt hD))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
        rewrite (isAllZeroRunsK_spec hz), evalRuns_pushRunK, evalR_pushRunK, !npow_1;
          cbn [evalRuns]; unfold evalSym.
        exact (rule_MJ_default (evalR Rh Rt d0)). }
    destruct L as [| [lw lk] L']; [exact (hrestL h) |].
    destruct lw as [| | ba bc | | | | | | | |]; try exact (hrestL h).
    (* lw = SB ba bc *)
    split_opt h csub hcoll.
    + destruct Rh as [| r0 rrest]; [discriminate |].
      destruct (if N.eqb (bc mod 3) 2 then N.leb 1 ba else false) eqn:hcond; [| discriminate].
      destruct (N.eqb (bc mod 3) 2) eqn:hbc2; [| discriminate].
      apply N.eqb_eq in hbc2; apply N.leb_le in hcond.
      set (stepH := bc / 3 + 1) in *.
      set (av := N.div2 (peekCollZAvailK (r0 :: rrest) Rt d0) / stepH) in *.
      set (mc := if N.leb lk av then lk else av) in *.
      destruct (N.eqb mc 0) eqn:hmc0; [discriminate |].
      apply N.eqb_neq in hmc0.
      assert (hmc_le : 1 <= mc /\ mc <= lk).
      { unfold mc; destruct (N.leb lk av) eqn:hlk;
          [apply N.leb_le in hlk | apply N.leb_gt in hlk]; lia. }
      destruct hmc_le as [hmc1 hmc_lk].
      set (need := mc * stepH) in *.
      assert (hneed1 : 1 <= need) by (unfold need, stepH; nia).
      pose proof (doCallsNoneK_sound (r0 :: rrest) Rt d0 need false hneed1 hRh hRt hD) as hdc.
      destruct (doCallsNoneK (r0 :: rrest) Rt d0 need false) as [[[hd nRh] nRt] nD0].
      destruct hdc as [pnRh [pnRt [dnRt [_ hnc]]]].
      destruct (N.eqb hd need) eqn:hhd; [| discriminate].
      apply N.eqb_eq in hhd; subst hd.
      set (L1 := if N.eqb lk mc then L' else mkRun (SB ba bc) (lk - mc) :: L') in *.
      assert (hL1 : AllPos L1 /\
        evalRuns (mkRun (SB ba bc) lk :: L') 0inf = npow (B_word ba bc) mc *> evalRuns L1 0inf).
      { unfold L1. destruct (N.eqb lk mc) eqn:hlkmc.
        - apply N.eqb_eq in hlkmc; rewrite hlkmc. exact (conj (proj2 hL) eq_refl).
        - apply N.eqb_neq in hlkmc.
          split; [simpl; split; [lia | exact (proj2 hL)] |].
          cbn [evalRuns]; unfold evalSym.
          replace lk with (mc + (lk - mc)) at 1 by lia.
          rewrite <- npow_append_npow. reflexivity. }
      destruct hL1 as [hpL1 heL1].
      pose proof (pushRDK_spec (ba + 1) mc nRh nRt nD0 pnRh pnRt dnRt) as hp1.
      destruct (pushRDK (ba + 1) mc nRh nRt) as [nRh1 nRt1].
      inversion hcoll; subst.
      destruct hp1 as [p1 [q1 [d1h e1]]].
      split; [exact (conj hpL1 (conj p1 (conj q1 d1h))) |].
      unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0].
      rewrite heL1, e1.
      pose proof (B_word_MJ_r2_pow (ba - 1) (bc / 3) mc (evalRuns L1 0inf)
        (evalR (r0 :: rrest) Rt d0) (evalR nRh nRt nD0) hnc) as hstep.
      replace (1 + (ba - 1)) with ba in hstep by lia.
      replace (2 + (ba - 1)) with (ba + 1) in hstep by lia.
      replace (3 * (bc / 3) + 2) with bc in hstep by lia.
      exact hstep.
    + set (L1 := decRunK (SB ba bc) lk L') in *.
      pose proof (evalRuns_decRunK (SB ba bc) lk L' 0inf (proj1 hL)) as hdec.
      pose proof (AllPos_decRunK (SB ba bc) lk (proj2 hL)) as hpL1.
      destruct (if N.leb 1 ba then N.leb 3 bc else false) eqn:hc3.
      * destruct (N.leb 1 ba); [| discriminate].
        apply N.leb_le in hc3.
        inversion h; subst.
        split; [exact (conj (AllPos_pushBK (ba + 1) (bc - 3) 1 hpL1) (conj hRh (conj hRt hD))) |].
        unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
        rewrite <- hdec, evalRuns_pushBK, npow_1; unfold evalSym.
        exact (B_word_turnJ ba bc hc3 (evalRuns L1 0inf) (evalR Rh Rt d0)).
      * destruct (if N.leb 1 ba then N.eqb bc 2 else false) eqn:hc2.
        -- destruct (N.leb 1 ba); [| discriminate].
           apply N.eqb_eq in hc2; subst bc.
           inversion h; subst.
           split; [exact (conj (AllPos_pushRunK Sw10 (ba + 1) (AllPos_pushRunK Sw01 1 (AllPos_pushRunK (SS 0) 1 hpL1)))
             (conj hRh (conj hRt hD))) |].
           unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
           rewrite <- hdec, !evalRuns_pushRunK, !npow_1; unfold evalSym.
           exact (B_word_turnJ_2 ba (evalRuns L1 0inf) (evalR Rh Rt d0)).
        -- inversion h; subst.
           split; [exact (conj (AllPos_pushRunK Sw10 ba (AllPos_pushRunK Sb1 bc (AllPos_pushRunK (SS 0) 2 hpL1)))
             (conj hRh (conj hRt hD))) |].
           unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns].
           rewrite <- hdec, evalRuns_B_unpack; unfold evalSym.
           exact (evstep_refl tm _).
Qed.

Lemma stepK_sound (f64 f4096 : nat) (c c' : FastCfg)
  (hv : ValidCfg c) (h : stepK f64 f4096 c = Some c') :
  ValidCfg c' /\ evalCfg c -->* evalCfg c'.
Proof.
  destruct c as [m L Rh Rt d0].
  destruct hv as [hL [hRh [hRt hD]]].
  unfold stepK, evalCfg in *; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0] in *.
  destruct m.
  - exact (stepMRK_sound f64 f4096 L Rh Rt d0 c' hL hRh hRt hD h).
  - exact (stepMLK_sound f64 f4096 L Rh Rt d0 c' hL hRh hRt hD h).
  - exact (stepMJK_sound f64 f4096 L Rh Rt d0 c' hL hRh hRt hD h).
Qed.

(* ========================================================================== *)
(* Section 5: Trajectory Iteration & Top-Level Halting Soundness              *)
(* ========================================================================== *)

Lemma iter_stepOpt_none (f64 f4096 : nat) (p : positive) :
  Pos.iter (stepOpt f64 f4096) None p = None.
Proof.
  induction p as [p ih | p ih |]; simpl; rewrite ?ih; reflexivity.
Qed.

Lemma stepOpt_some_inv (f64 f4096 : nat) (st : option FastCfg) (c' : FastCfg)
  (h : stepOpt f64 f4096 st = Some c') :
  exists c0, st = Some c0 /\ stepK f64 f4096 c0 = Some c'.
Proof.
  destruct st as [c0 |]; simpl in h; [exists c0; exact (conj eq_refl h) | discriminate].
Qed.

Lemma iter_stepOpt_some_inv (f64 f4096 : nat) (p : positive) (st : option FastCfg) (c' : FastCfg)
  (h : Pos.iter (stepOpt f64 f4096) st p = Some c') :
  exists c0, st = Some c0.
Proof.
  destruct st as [c0 |]; [exists c0; reflexivity | rewrite iter_stepOpt_none in h; discriminate].
Qed.

Lemma iter_stepOpt_sound (f64 f4096 : nat) (p : positive) :
  forall (c c' : FastCfg),
    ValidCfg c ->
    Pos.iter (stepOpt f64 f4096) (Some c) p = Some c' ->
    ValidCfg c' /\ evalCfg c -->* evalCfg c'.
Proof.
  induction p as [p ih | p ih |]; intros c c' hv h.
  - simpl in h.
    destruct (stepOpt_some_inv f64 f4096 _ c' h) as [c2 [h2 hs]].
    destruct (iter_stepOpt_some_inv f64 f4096 p _ c2 h2) as [c1 h1].
    rewrite h1 in h2.
    destruct (ih c c1 hv h1) as [hv1 hr1].
    destruct (ih c1 c2 hv1 h2) as [hv2 hr2].
    destruct (stepK_sound f64 f4096 c2 c' hv2 hs) as [hv' hr3].
    split; [exact hv' |].
    eapply evstep_trans; [exact hr1 | eapply evstep_trans; [exact hr2 | exact hr3]].
  - simpl in h.
    destruct (iter_stepOpt_some_inv f64 f4096 p _ c' h) as [c1 h1].
    rewrite h1 in h.
    destruct (ih c c1 hv h1) as [hv1 hr1].
    destruct (ih c1 c' hv1 h) as [hv' hr2].
    split; [exact hv' |].
    eapply evstep_trans; [exact hr1 | exact hr2].
  - simpl in h.
    exact (stepK_sound f64 f4096 c c' hv h).
Qed.

Lemma cp_0_valid : ValidCfg cp_0.
Proof.
  unfold ValidCfg, cp_0; simpl; repeat (split; try lia; try exact I).
Qed.

Lemma init_to_cp0 : c0 -->* evalCfg cp_0.
Proof.
  unfold evalCfg, cp_0, evalR; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0 evalRuns evalSym].
  rewrite !npow_1, npow_0; cbn [Str_app].
  exact rule_init.
Qed.

Lemma isHaltedK_halts (c : FastCfg) (hv : ValidCfg c) (h : isHaltedK c = true) :
  halts tm (evalCfg c).
Proof.
  destruct c as [m L Rh Rt d0].
  unfold isHaltedK in h; cbn [cfg_mode cfg_L] in h.
  destruct m; try discriminate.
  destruct (takeBits5RunsK false false true true true L) as [L' |] eqn:ht; [| discriminate].
  destruct (takeBits5RunsK_spec false false true true true L L' (proj1 hv) ht) as [_ he].
  unfold evalCfg; cbn [cfg_mode cfg_L cfg_Rh cfg_Rt cfg_d0]; rewrite he; unfold bitSym.
  exact (rule_halt (evalRuns L' 0inf) (evalR Rh Rt d0)).
Qed.

Lemma runHalted_sound (p : positive) (c : FastCfg)
  (hv : ValidCfg c) (h : runHalted p c = true) :
  halts tm (evalCfg c).
Proof.
  unfold runHalted in h; cbv zeta in h.
  destruct (Pos.iter (stepOpt (Nat.pow 2 6) (Nat.pow 2 12)) (Some c) p) as [c' |] eqn:hit;
    [| discriminate].
  destruct (iter_stepOpt_sound (Nat.pow 2 6) (Nat.pow 2 12) p c c' hv hit) as [hv' hreach].
  exact (evstep_halts (evalCfg c) (evalCfg c') hreach (isHaltedK_halts c' hv' h)).
Qed.

Lemma traj_halted : runHalted 1240545%positive cp_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

End M339.

Theorem halt : halts tm c0.
Proof.
  exact (M339.evstep_halts c0 (M339.evalCfg M339.cp_0) M339.init_to_cp0
    (M339.runHalted_sound 1240545%positive M339.cp_0 M339.cp_0_valid M339.traj_halted)).
Qed.
