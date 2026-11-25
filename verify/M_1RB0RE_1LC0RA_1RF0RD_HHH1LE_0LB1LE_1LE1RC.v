(* 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat ZifyN NArith PArith PeanoNat Lists.Streams List String Bool.
Import ListNotations.

Set Default Goal Selector "!".

Open Scope list_scope.
Open Scope nat_scope.

Definition tm : TM := TM_from_str "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC".

Definition tm_aux : TM := Eval compute in
  (TM_from_str "1RB0LF_1LC0LD_1RE1LB_---1RE_0RA1RE_1LA0LE").

Local Arguments tm _ : simpl never.
Local Arguments tm_aux _ : simpl never.

Local Notation b0 := (S0 : Sym).
Local Notation b1 := (S1 : Sym).

(* ========================================================================== *)
(* Layer 1: Auxiliary Mirrored Machine, Tape Lemmas, and Macro Transitions    *)
(* ========================================================================== *)

Definition perm_q (q : Q) : Q :=
  match q with
  | A => B
  | B => C
  | C => F
  | D => D
  | E => E
  | F => A
  end.

Definition mirror_cfg (c : Q * tape) : Q * tape :=
  let '(q, (l, s, r)) := c in (perm_q q, (r, s, l)).

Lemma step_mirror (c1 c2 : Q * tape) :
  c1 -[ tm_aux ]-> c2 -> mirror_cfg c1 -[ tm ]-> mirror_cfg c2.
Proof.
  intro H.
  inversion H as [q q' s s' l r Htr | q q' s s' l r Htr]; subst;
    destruct q, s; inversion Htr; subst; simpl;
    first [ apply @step_left; reflexivity | apply @step_right; reflexivity ].
Qed.

Lemma progress_mirror (c1 c2 : Q * tape) :
  c1 -[ tm_aux ]->+ c2 -> mirror_cfg c1 -[ tm ]->+ mirror_cfg c2.
Proof.
  induction 1 as [c1 c2 H | c1 c2 c3 H _ IH].
  - exact (progress_base (step_mirror c1 c2 H)).
  - exact (progress_step (step_mirror c1 c2 H) IH).
Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app app lpow].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac run_steps :=
  rewrite ?Nat.add_succ_r, ?Nat.add_0_r;
  cbn [lpow app Str_app];
  do 40 try (try solve [fast_finish]; fast_step);
  fast_finish.

Ltac run_plus :=
  rewrite ?Nat.add_succ_r, ?Nat.add_0_r;
  cbn [lpow app Str_app];
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  do 40 try (try solve [fast_finish]; fast_step);
  fast_finish.

Lemma etrans {m : TM} {c1 c2 c3 : Q * tape} :
  c1 -[ m ]->* c2 -> c2 -[ m ]->* c3 -> c1 -[ m ]->* c3.
Proof. apply evstep_trans. Qed.

Lemma ep_trans {m : TM} {c1 c2 c3 : Q * tape} :
  c1 -[ m ]->* c2 -> c2 -[ m ]->+ c3 -> c1 -[ m ]->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma pe_trans {m : TM} {c1 c2 c3 : Q * tape} :
  c1 -[ m ]->+ c2 -> c2 -[ m ]->* c3 -> c1 -[ m ]->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma ptrans {m : TM} {c1 c2 c3 : Q * tape} :
  c1 -[ m ]->+ c2 -> c2 -[ m ]->+ c3 -> c1 -[ m ]->+ c3.
Proof. apply progress_trans. Qed.

Lemma zPar (u : list Sym) (m n : nat) (r : side) :
  u ^^ (m + n) *> r = u ^^ m *> (u ^^ n *> r).
Proof.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma zPsr (u : list Sym) (n : nat) (r : side) :
  u ^^ (n + 1) *> r = u *> (u ^^ n *> r).
Proof.
  rewrite Nat.add_1_r. cbn [lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Lemma zPl (s : side) (u : list Sym) (m n : nat) :
  s <* u ^^ (m + n) = (s <* u ^^ m) <* u ^^ n.
Proof.
  rewrite Nat.add_comm. apply zPar.
Qed.

Lemma zPa1 (u : list Sym) (k : nat) (r : side) :
  u ^^ k *> (u *> r) = u ^^ (k + 1) *> r.
Proof.
  rewrite Nat.add_1_r. cbn [lpow].
  rewrite <- Str_app_assoc, lpow_shift, Str_app_assoc. reflexivity.
Qed.

Lemma zPal (l : side) (u : list Sym) (k : nat) :
  (l <* u) <* u ^^ k = l <* u ^^ (k + 1).
Proof.
  apply zPa1.
Qed.

Lemma append_zero_pow_01 (s : side) (k : nat) :
  (s <* [b0]) <* [b0; b1] ^^ k = (s <* [b1; b0] ^^ k) <* [b0].
Proof.
  exact (lpow_rotate [b1] b0 s k).
Qed.

Lemma default_pow_01 (c : nat) :
  const b0 <* [b0; b1] ^^ c = (const b0 <* [b1; b0] ^^ c) <* [b0].
Proof.
  exact (lpow_rotate_const0 [b1] c).
Qed.

Lemma append_one_pow_10 (s : side) (k : nat) :
  (s <* [b1]) <* [b1; b0] ^^ k = (s <* [b0; b1] ^^ k) <* [b1].
Proof.
  exact (lpow_rotate [b0] b1 s k).
Qed.

Lemma pow_11_eq_pow_1_mul2 (k : nat) :
  [b1; b1] ^^ k = [b1] ^^ (2 * k).
Proof.
  rewrite Nat.mul_comm. symmetry. exact (lpow_mul [b1] k 2).
Qed.

Lemma pow_01_append_0 (k : nat) (r : side) :
  [b0; b1] ^^ k *> ([b0] *> r) = [b0] *> ([b1; b0] ^^ k *> r).
Proof.
  exact (lpow_rotate [b1] b0 r k).
Qed.

Lemma shift_E_ones (k : nat) (l r : side) :
  (l {{E}}> ([b1] ^^ k *> r)) -[ tm_aux ]->* ((l <* [b1] ^^ k) {{E}}> r).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite (zPsr [b1] k r).
    assert (h1 : (l {{E}}> ([b1] *> ([b1] ^^ k *> r))) -[ tm_aux ]->*
                 ((l <* [b1]) {{E}}> ([b1] ^^ k *> r))) by run_steps.
    pose proof (ih (l <* [b1]) r) as h2.
    rewrite (zPal l [b1] k) in h2.
    exact (etrans h1 h2).
Qed.

Lemma shift_CB_left (k : nat) (l r : side) :
  ((l <* [b0; b1] ^^ k) {{C}}> ([b1] *> r)) -[ tm_aux ]->*
  (l {{C}}> ([b1] *> ([b1; b1] ^^ k *> r))).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite (zPsr [b0; b1] k l).
    assert (h1 : (((l <* [b0; b1] ^^ k) <* [b0; b1]) {{C}}> ([b1] *> r)) -[ tm_aux ]->*
                 ((l <* [b0; b1] ^^ k) {{C}}> ([b1] *> ([b1; b1] *> r)))) by run_steps.
    pose proof (ih l ([b1; b1] *> r)) as h2.
    rewrite (zPa1 [b1; b1] k r) in h2.
    exact (etrans h1 h2).
Qed.

Lemma shift_D_right_100 (k : nat) (l r : side) :
  (l {{D}}> ([b1; b0; b0] *> ([b1; b0] ^^ k *> r))) -[ tm_aux ]->*
  ((l <* [b0; b1] ^^ k) {{D}}> ([b1; b0; b0] *> r)).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite (zPsr [b1; b0] k r).
    assert (h1 : (l {{D}}> ([b1; b0; b0] *> ([b1; b0] *> ([b1; b0] ^^ k *> r)))) -[ tm_aux ]->*
                 ((l <* [b0; b1]) {{D}}> ([b1; b0; b0] *> ([b1; b0] ^^ k *> r)))) by run_steps.
    pose proof (ih (l <* [b0; b1]) r) as h2.
    rewrite (zPal l [b0; b1] k) in h2.
    exact (etrans h1 h2).
Qed.

Lemma shift_FA_left (k : nat) (l r : side) :
  ((l <* [b1; b0] ^^ k) {{F}}> ([b0] *> r)) -[ tm_aux ]->*
  (l {{F}}> ([b0] *> ([b0; b1] ^^ k *> r))).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r.
  - cbn [lpow Str_app]. apply evstep_refl.
  - replace (S k) with (k + 1) by lia.
    rewrite (zPsr [b1; b0] k l).
    assert (h1 : (((l <* [b1; b0] ^^ k) <* [b1; b0]) {{F}}> ([b0] *> r)) -[ tm_aux ]->*
                 ((l <* [b1; b0] ^^ k) {{F}}> ([b0] *> ([b0; b1] *> r)))) by run_steps.
    pose proof (ih l ([b0; b1] *> r)) as h2.
    rewrite (zPa1 [b0; b1] k r) in h2.
    exact (etrans h1 h2).
Qed.

Definition E_cfg (a b : nat) : Q * tape :=
  ((const b0 <* [b1] ^^ b) <* [b1; b0] ^^ a) {{E}}> const b0.

Definition F_R (b k : nat) (r : side) : Q * tape :=
  ((const b0 <* [b1] ^^ b) <* [b1; b0] ^^ k) {{F}}> ([b0; b0] *> r).

Definition F_cfg (b k c : nat) : Q * tape :=
  ((const b0 <* [b1] ^^ b) <* [b1; b0] ^^ k) {{F}}> ([b0; b0] *> ([b1] ^^ c *> const b0)).

Lemma F_cfg_eq_F_R (b k c : nat) :
  F_cfg b k c = F_R b k ([b1] ^^ c *> const b0).
Proof. reflexivity. Qed.

Theorem step_E_b3_to_F (a b : nat) :
  E_cfg a (b + 3) -[ tm_aux ]->+ F_cfg (b + 1) 0 (2 * a + 3).
Proof.
  unfold E_cfg, F_cfg. cbn [lpow app Str_app].
  assert (h1 : (((const b0 <* [b1] ^^ (b + 3)) <* [b1; b0] ^^ a) {{E}}> const b0) -[ tm_aux ]->+
               ((((const b0 <* [b1] ^^ (b + 3)) <* [b1; b0] ^^ a) <* [b0]) {{C}}>
                 ([b1] *> ([b1] *> const b0)))) by run_plus.
  rewrite <- (append_zero_pow_01 (const b0 <* [b1] ^^ (b + 3)) a) in h1.
  pose proof (shift_CB_left a ((const b0 <* [b1] ^^ (b + 3)) <* [b0]) ([b1] *> const b0)) as h2.
  rewrite (pow_11_eq_pow_1_mul2 a) in h2.
  replace (b + 3) with ((b + 1) + 2) in h1, h2 |- * by lia.
  rewrite (zPl (const b0) [b1] (b + 1) 2) in h1, h2 |- *.
  assert (h3 : (((((const b0 <* [b1] ^^ (b + 1)) <* [b1] ^^ 2) <* [b0]) {{C}}>
                 ([b1] *> ([b1] ^^ (2 * a) *> ([b1] *> const b0)))) -[ tm_aux ]->+
               ((const b0 <* [b1] ^^ (b + 1)) {{F}}>
                 ([b0; b0] *> ([b1] ^^ 2 *> ([b1] ^^ (2 * a) *> ([b1] ^^ 1 *> const b0))))))) by run_plus.
  rewrite <- (zPar [b1] (2 * a) 1 (const b0)) in h3.
  rewrite <- (zPar [b1] 2 (2 * a + 1) (const b0)) in h3.
  replace (2 + (2 * a + 1)) with (2 * a + 3) in h3 by lia.
  exact (ptrans (pe_trans h1 h2) h3).
Qed.

Theorem step_F_b2_k0 (c : nat) :
  F_cfg 2 0 (c + 1) -[ tm_aux ]->+ F_cfg 5 0 c.
Proof.
  unfold F_cfg.
  rewrite (zPsr [b1] c (const b0)).
  run_plus.
Qed.

Definition D100 (b k : nat) (r : side) : Q * tape :=
  (((const b0 <* [b1] ^^ b) <* [b1; b0] ^^ k) <* [b0]) {{D}}> ([b1; b0; b0] *> r).

Definition C_bounce (b : nat) (s : side) : Q * tape :=
  ((const b0 <* [b1] ^^ b) <* [b0]) {{C}}> ([b1] *> s).

Lemma step_F0_sweep_right (k : nat) (r : side) :
  (const b0 {{F}}> ([b0; b0] *> ([b1; b0] ^^ k *> r))) -[ tm_aux ]->+
  ((const b0 <* [b0; b1] ^^ k) {{D}}> ([b1; b0; b0] *> r)).
Proof.
  assert (h1 : (const b0 {{F}}> ([b0; b0] *> ([b1; b0] ^^ k *> r))) -[ tm_aux ]->+
               (const b0 {{D}}> ([b1; b0; b0] *> ([b1; b0] ^^ k *> r)))) by run_plus.
  pose proof (shift_D_right_100 k (const b0) r) as h2.
  exact (pe_trans h1 h2).
Qed.

Lemma F_R_b0_to_D100 (k : nat) (r : side) :
  F_R 0 k r -[ tm_aux ]->+ D100 0 k r.
Proof.
  unfold F_R, D100. cbn [lpow Str_app].
  pose proof (shift_FA_left k (const b0) ([b0] *> r)) as h1.
  rewrite (pow_01_append_0 k r) in h1.
  pose proof (step_F0_sweep_right k r) as h2.
  rewrite (default_pow_01 k) in h2.
  exact (ep_trans h1 h2).
Qed.

Lemma F_R_b1_to_D100 (k : nat) (r : side) :
  F_R 1 k r -[ tm_aux ]->+ D100 0 (k + 1) r.
Proof.
  unfold F_R, D100.
  pose proof (shift_FA_left k (const b0 <* [b1] ^^ 1) ([b0] *> r)) as h1.
  rewrite (pow_01_append_0 k r) in h1.
  assert (h2 : ((const b0 <* [b1] ^^ 1) {{F}}> ([b0] *> ([b0] *> ([b1; b0] ^^ k *> r)))) -[ tm_aux ]->+
               (const b0 {{F}}> ([b0; b0] *> ([b1; b0] *> ([b1; b0] ^^ k *> r))))) by run_plus.
  rewrite <- (zPsr [b1; b0] k r) in h2.
  pose proof (step_F0_sweep_right (k + 1) r) as h3.
  rewrite (default_pow_01 (k + 1)) in h3.
  cbn [lpow Str_app] in *.
  exact (ptrans (ep_trans h1 h2) h3).
Qed.

Lemma F_R_b3_to_D100 (b k : nat) (r : side) :
  F_R (b + 3) k r -[ tm_aux ]->+ D100 (b + 1) k r.
Proof.
  unfold F_R, D100.
  pose proof (shift_FA_left k (const b0 <* [b1] ^^ (b + 3)) ([b0] *> r)) as h1.
  rewrite (pow_01_append_0 k r) in h1.
  replace (b + 3) with ((b + 1) + 2) in h1 |- * by lia.
  rewrite (zPl (const b0) [b1] (b + 1) 2) in h1 |- *.
  assert (h2 : (((const b0 <* [b1] ^^ (b + 1)) <* [b1] ^^ 2) {{F}}>
                 ([b0] *> ([b0] *> ([b1; b0] ^^ k *> r)))) -[ tm_aux ]->+
               (((const b0 <* [b1] ^^ (b + 1)) <* [b0]) {{D}}>
                 ([b1; b0; b0] *> ([b1; b0] ^^ k *> r)))) by run_plus.
  pose proof (shift_D_right_100 k ((const b0 <* [b1] ^^ (b + 1)) <* [b0]) r) as h3.
  rewrite (append_zero_pow_01 (const b0 <* [b1] ^^ (b + 1)) k) in h3.
  cbn [Str_app] in h1.
  exact (pe_trans (ep_trans h1 h2) h3).
Qed.

Lemma D100_0_11 (k : nat) (r : side) :
  D100 0 k ([b1; b1] *> r) -[ tm_aux ]->+ F_R 1 (k + 1) r.
Proof.
  unfold D100, F_R. cbn [lpow Str_app].
  change (b0 >> ([b1; b0] ^^ k *> const b0)) with ((const b0 <* [b1; b0] ^^ k) <* [b0]).
  rewrite <- (default_pow_01 k).
  assert (h1 : (((const b0 <* [b0; b1] ^^ k) {{D}}> ([b1; b0; b0] *> ([b1; b1] *> r))) -[ tm_aux ]->+
               ((((const b0 <* [b0; b1] ^^ k) <* [b0; b1] ^^ 1) <* [b1]) {{F}}> ([b0; b0] *> r)))) by run_plus.
  rewrite <- (zPl (const b0) [b0; b1] k 1) in h1.
  rewrite <- (append_one_pow_10 (const b0) (k + 1)) in h1.
  exact h1.
Qed.

Lemma D100_succ_11 (b k : nat) (r : side) :
  D100 (b + 1) k ([b1; b1] *> r) -[ tm_aux ]->+ F_R (b + 1) (k + 2) r.
Proof.
  unfold D100, F_R.
  assert (h1 : ((((const b0 <* [b1] ^^ (b + 1)) <* [b1; b0] ^^ k) <* [b0]) {{D}}>
                 ([b1; b0; b0] *> ([b1; b1] *> r))) -[ tm_aux ]->+
               ((((const b0 <* [b1] ^^ (b + 1)) <* [b1; b0] ^^ k) <* [b1; b0] ^^ 2) {{F}}>
                 ([b0; b0] *> r))) by run_plus.
  rewrite <- (zPl (const b0 <* [b1] ^^ (b + 1)) [b1; b0] k 2) in h1.
  exact h1.
Qed.

Lemma D100_nil_to_C_bounce (b k : nat) :
  D100 b k (const b0) -[ tm_aux ]->+ C_bounce b ([b1] ^^ (2 * k + 3) *> const b0).
Proof.
  unfold D100, C_bounce.
  rewrite <- (append_zero_pow_01 (const b0 <* [b1] ^^ b) k).
  assert (h1 : ((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) {{D}}>
                 ([b1; b0; b0] *> const b0)) -[ tm_aux ]->+
               (((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) <* [b0; b1] ^^ 1) {{C}}>
                 ([b1] *> ([b1] ^^ 1 *> const b0)))) by run_plus.
  rewrite <- (zPl ((const b0 <* [b1] ^^ b) <* [b0]) [b0; b1] k 1) in h1.
  pose proof (shift_CB_left (k + 1) ((const b0 <* [b1] ^^ b) <* [b0]) ([b1] ^^ 1 *> const b0)) as h2.
  rewrite (pow_11_eq_pow_1_mul2 (k + 1)) in h2.
  rewrite <- (zPar [b1] (2 * (k + 1)) 1 (const b0)) in h2.
  replace (2 * (k + 1) + 1) with (2 * k + 3) in h2 by lia.
  exact (pe_trans h1 h2).
Qed.

Lemma D100_one_to_C_bounce (b k : nat) :
  D100 b k ([b1] *> const b0) -[ tm_aux ]->+ C_bounce b ([b1] ^^ (2 * k + 5) *> const b0).
Proof.
  unfold D100, C_bounce.
  rewrite <- (append_zero_pow_01 (const b0 <* [b1] ^^ b) k).
  assert (h1 : ((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) {{D}}>
                 ([b1; b0; b0] *> ([b1] *> const b0))) -[ tm_aux ]->+
               (((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) <* [b0; b1] ^^ 2) {{C}}>
                 ([b1] *> ([b1] ^^ 1 *> const b0)))) by run_plus.
  rewrite <- (zPl ((const b0 <* [b1] ^^ b) <* [b0]) [b0; b1] k 2) in h1.
  pose proof (shift_CB_left (k + 2) ((const b0 <* [b1] ^^ b) <* [b0]) ([b1] ^^ 1 *> const b0)) as h2.
  rewrite (pow_11_eq_pow_1_mul2 (k + 2)) in h2.
  rewrite <- (zPar [b1] (2 * (k + 2)) 1 (const b0)) in h2.
  replace (2 * (k + 2) + 1) with (2 * k + 5) in h2 by lia.
  exact (pe_trans h1 h2).
Qed.

Lemma D100_01_to_C_bounce (b k : nat) (r : side) :
  D100 b k ([b0; b1] *> r) -[ tm_aux ]->+ C_bounce b ([b1] ^^ (2 * k + 4) *> r).
Proof.
  unfold D100, C_bounce.
  rewrite <- (append_zero_pow_01 (const b0 <* [b1] ^^ b) k).
  assert (h1 : ((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) {{D}}>
                 ([b1; b0; b0] *> ([b0; b1] *> r))) -[ tm_aux ]->+
               (((((const b0 <* [b1] ^^ b) <* [b0]) <* [b0; b1] ^^ k) <* [b0; b1] ^^ 1) {{C}}>
                 ([b1] *> ([b1] ^^ 2 *> r)))) by run_plus.
  rewrite <- (zPl ((const b0 <* [b1] ^^ b) <* [b0]) [b0; b1] k 1) in h1.
  pose proof (shift_CB_left (k + 1) ((const b0 <* [b1] ^^ b) <* [b0]) ([b1] ^^ 2 *> r)) as h2.
  rewrite (pow_11_eq_pow_1_mul2 (k + 1)) in h2.
  rewrite <- (zPar [b1] (2 * (k + 1)) 2 r) in h2.
  replace (2 * (k + 1) + 2) with (2 * k + 4) in h2 by lia.
  exact (pe_trans h1 h2).
Qed.

Lemma C_bounce_0 (s : side) :
  C_bounce 0 s -[ tm_aux ]->+ ((const b0 <* [b1] ^^ 3) {{E}}> s).
Proof.
  unfold C_bounce. run_plus.
Qed.

Lemma C_bounce_1 (s : side) :
  C_bounce 1 s -[ tm_aux ]->+ ((const b0 <* [b1] ^^ 5) {{E}}> s).
Proof.
  unfold C_bounce. run_plus.
Qed.

Lemma C_bounce_3 (b : nat) (s : side) :
  C_bounce (b + 3) s -[ tm_aux ]->+ F_R (b + 1) 0 ([b1] ^^ 2 *> s).
Proof.
  unfold C_bounce, F_R.
  replace (b + 3) with ((b + 1) + 2) by lia.
  rewrite (zPl (const b0) [b1] (b + 1) 2).
  run_plus.
Qed.

Lemma step_F_ksucc_c0 (b k : nat) :
  F_cfg b (k + 1) 0 -[ tm_aux ]->+ F_cfg b k 1.
Proof.
  unfold F_cfg.
  rewrite (zPl (const b0 <* [b1] ^^ b) [b1; b0] k 1).
  run_plus.
Qed.

Lemma step_F_b2_k0_c0 :
  F_cfg 2 0 0 -[ tm_aux ]->+ F_cfg 3 0 3.
Proof.
  unfold F_cfg. run_plus.
Qed.

Lemma C_bounce_0_ones (n : nat) :
  C_bounce 0 ([b1] ^^ n *> const b0) -[ tm_aux ]->+ F_cfg (n + 1) 0 3.
Proof.
  pose proof (C_bounce_0 ([b1] ^^ n *> const b0)) as h1.
  pose proof (shift_E_ones n (const b0 <* [b1] ^^ 3) (const b0)) as h2.
  rewrite <- (zPl (const b0) [b1] 3 n) in h2.
  replace (3 + n) with (n + 3) in h2 by lia.
  change ((const b0 <* [b1] ^^ (n + 3)) {{E}}> const b0) with (E_cfg 0 (n + 3)) in h2.
  exact (ptrans (pe_trans h1 h2) (step_E_b3_to_F 0 n)).
Qed.

Lemma C_bounce_1_ones (n : nat) :
  C_bounce 1 ([b1] ^^ n *> const b0) -[ tm_aux ]->+ F_cfg (n + 3) 0 3.
Proof.
  pose proof (C_bounce_1 ([b1] ^^ n *> const b0)) as h1.
  pose proof (shift_E_ones n (const b0 <* [b1] ^^ 5) (const b0)) as h2.
  rewrite <- (zPl (const b0) [b1] 5 n) in h2.
  replace (5 + n) with ((n + 2) + 3) in h2 by lia.
  change ((const b0 <* [b1] ^^ ((n + 2) + 3)) {{E}}> const b0) with (E_cfg 0 ((n + 2) + 3)) in h2.
  pose proof (step_E_b3_to_F 0 (n + 2)) as h3.
  replace ((n + 2) + 1) with (n + 3) in h3 by lia.
  exact (ptrans (pe_trans h1 h2) h3).
Qed.

Lemma C_bounce_3_ones (b n : nat) :
  C_bounce (b + 3) ([b1] ^^ n *> const b0) -[ tm_aux ]->+ F_cfg (b + 1) 0 (n + 2).
Proof.
  pose proof (C_bounce_3 b ([b1] ^^ n *> const b0)) as h1.
  rewrite <- (zPar [b1] 2 n (const b0)), <- F_cfg_eq_F_R in h1.
  replace (2 + n) with (n + 2) in h1 by lia.
  exact h1.
Qed.

Theorem rule_F_ksucc_c0 (b k : nat) :
  F_cfg b (k + 1) 0 -[ tm_aux ]->+ F_cfg b k 1.
Proof. exact (step_F_ksucc_c0 b k). Qed.

Theorem rule_F_b0_k0_c0 :
  F_cfg 0 0 0 -[ tm_aux ]->+ F_cfg 4 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b0_to_D100 0 (const b0)) (D100_nil_to_C_bounce 0 0)) (C_bounce_0_ones 3)).
Qed.

Theorem rule_F_b1_k0_c0 :
  F_cfg 1 0 0 -[ tm_aux ]->+ F_cfg 6 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b1_to_D100 0 (const b0)) (D100_nil_to_C_bounce 0 1)) (C_bounce_0_ones 5)).
Qed.

Theorem rule_F_b2_k0_c0 :
  F_cfg 2 0 0 -[ tm_aux ]->+ F_cfg 3 0 3.
Proof. exact step_F_b2_k0_c0. Qed.

Theorem rule_F_b3_k0_c0 :
  F_cfg 3 0 0 -[ tm_aux ]->+ F_cfg 6 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b3_to_D100 0 0 (const b0)) (D100_nil_to_C_bounce 1 0)) (C_bounce_1_ones 3)).
Qed.

Theorem rule_F_b5_k0_c0 (b : nat) :
  F_cfg (b + 5) 0 0 -[ tm_aux ]->+ F_cfg (b + 1) 0 5.
Proof.
  replace (b + 5) with ((b + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (b + 2) 0 (const b0)) as h1.
  replace ((b + 2) + 1) with (b + 3) in h1 by lia.
  exact (ptrans (ptrans h1 (D100_nil_to_C_bounce (b + 3) 0))
                (C_bounce_3_ones b 3)).
Qed.

Theorem rule_F_b0_c1 (k : nat) :
  F_cfg 0 k 1 -[ tm_aux ]->+ F_cfg (2 * k + 6) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b0_to_D100 k ([b1] *> const b0)) (D100_one_to_C_bounce 0 k))
                     (C_bounce_0_ones (2 * k + 5))) as h.
  replace ((2 * k + 5) + 1) with (2 * k + 6) in h by lia.
  exact h.
Qed.

Theorem rule_F_b1_c1 (k : nat) :
  F_cfg 1 k 1 -[ tm_aux ]->+ F_cfg (2 * k + 8) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b1_to_D100 k ([b1] *> const b0)) (D100_one_to_C_bounce 0 (k + 1)))
                     (C_bounce_0_ones (2 * (k + 1) + 5))) as h.
  replace ((2 * (k + 1) + 5) + 1) with (2 * k + 8) in h by lia.
  exact h.
Qed.

Theorem rule_F_b2_k0_c1 (c : nat) :
  F_cfg 2 0 (c + 1) -[ tm_aux ]->+ F_cfg 5 0 c.
Proof. exact (step_F_b2_k0 c). Qed.

Theorem rule_F_b3_c1 (k : nat) :
  F_cfg 3 k 1 -[ tm_aux ]->+ F_cfg (2 * k + 8) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b3_to_D100 0 k ([b1] *> const b0)) (D100_one_to_C_bounce 1 k))
                     (C_bounce_1_ones (2 * k + 5))) as h.
  replace ((2 * k + 5) + 3) with (2 * k + 8) in h by lia.
  exact h.
Qed.

Theorem rule_F_b5_c1 (b k : nat) :
  F_cfg (b + 5) k 1 -[ tm_aux ]->+ F_cfg (b + 1) 0 (2 * k + 7).
Proof.
  replace (b + 5) with ((b + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (b + 2) k ([b1] *> const b0)) as h1.
  replace ((b + 2) + 1) with (b + 3) in h1 by lia.
  pose proof (ptrans (ptrans h1 (D100_one_to_C_bounce (b + 3) k))
                     (C_bounce_3_ones b (2 * k + 5))) as h.
  replace ((2 * k + 5) + 2) with (2 * k + 7) in h by lia.
  exact h.
Qed.

Theorem rule_F_b0_c2 (k c : nat) :
  F_cfg 0 k (c + 2) -[ tm_aux ]->+ F_cfg 1 (k + 1) c.
Proof.
  rewrite !F_cfg_eq_F_R.
  replace (c + 2) with (2 + c) by lia.
  rewrite (zPar [b1] 2 c (const b0)).
  exact (ptrans (F_R_b0_to_D100 k _) (D100_0_11 k ([b1] ^^ c *> const b0))).
Qed.

Theorem rule_F_b1_c2 (k c : nat) :
  F_cfg 1 k (c + 2) -[ tm_aux ]->+ F_cfg 1 (k + 2) c.
Proof.
  rewrite !F_cfg_eq_F_R.
  replace (c + 2) with (2 + c) by lia.
  rewrite (zPar [b1] 2 c (const b0)).
  pose proof (D100_0_11 (k + 1) ([b1] ^^ c *> const b0)) as h2.
  replace ((k + 1) + 1) with (k + 2) in h2 by lia.
  exact (ptrans (F_R_b1_to_D100 k _) h2).
Qed.

Theorem rule_F_b3_c2 (b k c : nat) :
  F_cfg (b + 3) k (c + 2) -[ tm_aux ]->+ F_cfg (b + 1) (k + 2) c.
Proof.
  rewrite !F_cfg_eq_F_R.
  replace (c + 2) with (2 + c) by lia.
  rewrite (zPar [b1] 2 c (const b0)).
  exact (ptrans (F_R_b3_to_D100 b k _) (D100_succ_11 b k ([b1] ^^ c *> const b0))).
Qed.

Lemma step_F_R_b2_one (k : nat) (r : side) :
  F_R 2 k ([b1] *> r) -[ tm_aux ]->+ F_R 5 0 ([b0; b1] ^^ k *> r).
Proof.
  unfold F_R. cbn [lpow Str_app].
  pose proof (shift_FA_left k (const b0 <* [b1] ^^ 2) ([b0; b1] *> r)) as h1.
  assert (h2 : ((const b0 <* [b1] ^^ 2) {{F}}> ([b0] *> ([b0; b1] ^^ k *> ([b0; b1] *> r)))) -[ tm_aux ]->+
               ((const b0 <* [b1] ^^ 5) {{F}}> ([b0; b0] *> ([b0; b1] ^^ k *> r)))).
  { rewrite (zPa1 [b0; b1] k r), (zPsr [b0; b1] k r). run_plus. }
  exact (ep_trans h1 h2).
Qed.

Lemma step_E_01_to_F_R (b : nat) (r : side) :
  ((const b0 <* [b1] ^^ b) {{E}}> ([b0; b1] *> r)) -[ tm_aux ]->+ F_R b 0 r.
Proof.
  unfold F_R. run_plus.
Qed.

Definition Odd_cfg (p k n m c : nat) : Q * tape :=
  F_R (2 * p + 1) k
    ([b1] ^^ (2 * n) *> ([b0; b1] ^^ (m + 1) *> ([b1] ^^ c *> const b0))).

Definition ETail_cfg (k m c : nat) : Q * tape :=
  (const b0 <* [b1] ^^ (2 * (k + 4) + 1)) {{E}}>
    ([b0; b1] ^^ m *> ([b1] ^^ c *> const b0)).

Theorem rule_F_b2_ksucc_c1 (k c : nat) :
  F_cfg 2 (k + 1) (c + 1) -[ tm_aux ]->+ Odd_cfg 2 0 0 k c.
Proof.
  unfold Odd_cfg. rewrite Nat.mul_0_r. cbn [lpow Str_app].
  rewrite F_cfg_eq_F_R, (zPsr [b1] c (const b0)).
  exact (step_F_R_b2_one (k + 1) ([b1] ^^ c *> const b0)).
Qed.

Theorem step_Odd_nsucc_p0 (k n m c : nat) :
  Odd_cfg 0 k (n + 1) m c -[ tm_aux ]->+ Odd_cfg 0 (k + 2) n m c.
Proof.
  unfold Odd_cfg.
  set (r := [b0; b1] ^^ (m + 1) *> ([b1] ^^ c *> const b0)).
  replace (2 * (n + 1)) with (2 + 2 * n) by lia.
  rewrite (zPar [b1] 2 (2 * n) r).
  pose proof (D100_0_11 (k + 1) ([b1] ^^ (2 * n) *> r)) as h2.
  replace ((k + 1) + 1) with (k + 2) in h2 by lia.
  exact (ptrans (F_R_b1_to_D100 k ([b1] ^^ 2 *> ([b1] ^^ (2 * n) *> r))) h2).
Qed.

Theorem step_Odd_nsucc_psucc (p k n m c : nat) :
  Odd_cfg (p + 1) k (n + 1) m c -[ tm_aux ]->+ Odd_cfg p (k + 2) n m c.
Proof.
  unfold Odd_cfg.
  set (r := [b0; b1] ^^ (m + 1) *> ([b1] ^^ c *> const b0)).
  replace (2 * (n + 1)) with (2 + 2 * n) by lia.
  replace (2 * (p + 1) + 1) with (2 * p + 3) by lia.
  rewrite (zPar [b1] 2 (2 * n) r).
  exact (ptrans (F_R_b3_to_D100 (2 * p) k ([b1] ^^ 2 *> ([b1] ^^ (2 * n) *> r)))
                (D100_succ_11 (2 * p) k ([b1] ^^ (2 * n) *> r))).
Qed.

Theorem step_Odd_n0_p0 (k m c : nat) :
  Odd_cfg 0 k 0 m c -[ tm_aux ]->+ ETail_cfg k m c.
Proof.
  unfold Odd_cfg, ETail_cfg. rewrite Nat.mul_0_r. cbn [lpow Str_app].
  rewrite (zPsr [b0; b1] m ([b1] ^^ c *> const b0)).
  set (r' := [b0; b1] ^^ m *> ([b1] ^^ c *> const b0)).
  pose proof (F_R_b1_to_D100 k ([b0; b1] *> r')) as h1.
  pose proof (D100_01_to_C_bounce 0 (k + 1) r') as h2.
  pose proof (C_bounce_0 ([b1] ^^ (2 * (k + 1) + 4) *> r')) as h3.
  pose proof (shift_E_ones (2 * (k + 1) + 4) (const b0 <* [b1] ^^ 3) r') as h4.
  rewrite <- (zPl (const b0) [b1] 3 (2 * (k + 1) + 4)) in h4.
  replace (3 + (2 * (k + 1) + 4)) with (2 * (k + 4) + 1) in h4 by lia.
  exact (pe_trans (ptrans (ptrans h1 h2) h3) h4).
Qed.

Theorem step_Odd_n0_p1 (k m c : nat) :
  Odd_cfg 1 k 0 m c -[ tm_aux ]->+ ETail_cfg k m c.
Proof.
  unfold Odd_cfg, ETail_cfg. rewrite Nat.mul_0_r. cbn [lpow Str_app].
  rewrite (zPsr [b0; b1] m ([b1] ^^ c *> const b0)).
  set (r' := [b0; b1] ^^ m *> ([b1] ^^ c *> const b0)).
  pose proof (F_R_b3_to_D100 0 k ([b0; b1] *> r')) as h1.
  pose proof (D100_01_to_C_bounce 1 k r') as h2.
  pose proof (C_bounce_1 ([b1] ^^ (2 * k + 4) *> r')) as h3.
  pose proof (shift_E_ones (2 * k + 4) (const b0 <* [b1] ^^ 5) r') as h4.
  rewrite <- (zPl (const b0) [b1] 5 (2 * k + 4)) in h4.
  replace (5 + (2 * k + 4)) with (2 * (k + 4) + 1) in h4 by lia.
  exact (pe_trans (ptrans (ptrans h1 h2) h3) h4).
Qed.

Theorem step_Odd_n0_p2_m0 (p k c : nat) :
  Odd_cfg (p + 2) k 0 0 c -[ tm_aux ]->+ F_cfg (2 * p + 1) 0 (2 * (k + 3) + c).
Proof.
  unfold Odd_cfg. rewrite Nat.mul_0_r.
  rewrite (zPsr [b0; b1] 0 ([b1] ^^ c *> const b0)).
  cbn [lpow Str_app].
  set (r' := [b1] ^^ c *> const b0).
  replace (2 * (p + 2) + 1) with ((2 * p + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (2 * p + 2) k ([b0; b1] *> r')) as h1.
  replace ((2 * p + 2) + 1) with (2 * p + 3) in h1 by lia.
  pose proof (D100_01_to_C_bounce (2 * p + 3) k r') as h2.
  replace (2 * p + 3) with ((2 * p) + 3) in h2 by lia.
  pose proof (C_bounce_3 (2 * p) ([b1] ^^ (2 * k + 4) *> r')) as h3.
  rewrite <- (zPar [b1] 2 (2 * k + 4) r') in h3.
  replace (2 + (2 * k + 4)) with (2 * (k + 3)) in h3 by lia.
  unfold r' in h3.
  rewrite <- (zPar [b1] (2 * (k + 3)) c (const b0)), <- F_cfg_eq_F_R in h3.
  exact (ptrans (ptrans h1 h2) h3).
Qed.

Theorem step_Odd_n0_p2_msucc (p k m c : nat) :
  Odd_cfg (p + 2) k 0 (m + 1) c -[ tm_aux ]->+ Odd_cfg p 0 (k + 3) m c.
Proof.
  unfold Odd_cfg. rewrite Nat.mul_0_r.
  rewrite (zPsr [b0; b1] (m + 1) ([b1] ^^ c *> const b0)).
  cbn [lpow app Str_app].
  set (r' := [b0; b1] ^^ (m + 1) *> ([b1] ^^ c *> const b0)).
  replace (2 * (p + 2) + 1) with ((2 * p + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (2 * p + 2) k ([b0; b1] *> r')) as h1.
  replace ((2 * p + 2) + 1) with (2 * p + 3) in h1 by lia.
  pose proof (D100_01_to_C_bounce (2 * p + 3) k r') as h2.
  replace (2 * p + 3) with ((2 * p) + 3) in h2 by lia.
  pose proof (C_bounce_3 (2 * p) ([b1] ^^ (2 * k + 4) *> r')) as h3.
  rewrite <- (zPar [b1] 2 (2 * k + 4) r') in h3.
  replace (2 + (2 * k + 4)) with (2 * (k + 3)) in h3 by lia.
  exact (ptrans (ptrans h1 h2) h3).
Qed.

Theorem step_ETail_m0 (k c : nat) :
  ETail_cfg k 0 c -[ tm_aux ]->+ F_cfg (2 * k + c + 7) 0 3.
Proof.
  unfold ETail_cfg. cbn [lpow Str_app].
  pose proof (shift_E_ones c (const b0 <* [b1] ^^ (2 * (k + 4) + 1)) (const b0)) as h1.
  rewrite <- (zPl (const b0) [b1] (2 * (k + 4) + 1) c) in h1.
  replace (2 * (k + 4) + 1 + c) with ((2 * k + c + 6) + 3) in h1 by lia.
  change ((const b0 <* [b1] ^^ ((2 * k + c + 6) + 3)) {{E}}> const b0)
    with (E_cfg 0 ((2 * k + c + 6) + 3)) in h1.
  pose proof (step_E_b3_to_F 0 (2 * k + c + 6)) as h2.
  replace ((2 * k + c + 6) + 1) with (2 * k + c + 7) in h2 by lia.
  exact (ep_trans h1 h2).
Qed.

Theorem step_ETail_m1 (k c : nat) :
  ETail_cfg k 1 c -[ tm_aux ]->+ F_cfg (2 * (k + 4) + 1) 0 c.
Proof.
  unfold ETail_cfg.
  cbn [lpow app Str_app].
  exact (step_E_01_to_F_R (2 * (k + 4) + 1) ([b1] ^^ c *> const b0)).
Qed.

Theorem step_ETail_m2 (k m c : nat) :
  ETail_cfg k (m + 2) c -[ tm_aux ]->+ Odd_cfg (k + 4) 0 0 m c.
Proof.
  unfold ETail_cfg, Odd_cfg. rewrite Nat.mul_0_r.
  replace (m + 2) with ((m + 1) + 1) by lia.
  rewrite (zPsr [b0; b1] (m + 1) ([b1] ^^ c *> const b0)).
  cbn [lpow app Str_app].
  exact (step_E_01_to_F_R (2 * (k + 4) + 1) ([b0; b1] ^^ (m + 1) *> ([b1] ^^ c *> const b0))).
Qed.

(* ========================================================================== *)
(* Layer 2: Symbolic Acceleration State Space (Binary N) & Soundness Bridge   *)
(* ========================================================================== *)

Open Scope N_scope.

Local Arguments N.add _ _ : simpl never.
Local Arguments N.sub _ _ : simpl never.
Local Arguments N.mul _ _ : simpl never.
Local Arguments N.div _ _ : simpl never.
Local Arguments N.pow _ _ : simpl never.

Lemma progress_congr {m : TM} {c1 c2 c1' c2' : Q * tape} :
  c1' -[ m ]->+ c2' -> c1 = c1' -> c2 = c2' -> c1 -[ m ]->+ c2.
Proof. intros H -> ->. exact H. Qed.

Ltac apply_rule R :=
  eapply progress_congr; [exact R | f_equal; lia | f_equal; lia].

Inductive State : Type :=
  | stA (b k c : N)
  | stOdd (p k n m c : N)
  | stETail (k m c : N).

Definition start : State := stA 4 0 3.

Definition next (s : State) : option State :=
  match s with
  | stA b k c =>
    if c =? 0 then
      if k =? 0 then
        if b =? 0 then Some (stA 4 0 3)
        else if b =? 1 then Some (stA 6 0 3)
        else if b =? 2 then Some (stA 3 0 3)
        else if b =? 3 then Some (stA 6 0 3)
        else if b =? 4 then None
        else Some (stA (b - 4) 0 5)
      else Some (stA b (k - 1) 1)
    else if c =? 1 then
      if b =? 0 then Some (stA (2 * k + 6) 0 3)
      else if b =? 1 then Some (stA (2 * k + 8) 0 3)
      else if b =? 2 then
        if k =? 0 then Some (stA 5 0 0)
        else Some (stOdd 2 0 0 (k - 1) 0)
      else if b =? 3 then Some (stA (2 * k + 8) 0 3)
      else if b =? 4 then None
      else Some (stA (b - 4) 0 (2 * k + 7))
    else
      if b =? 0 then Some (stA 1 (k + 1) (c - 2))
      else if b =? 1 then Some (stA 1 (k + 2) (c - 2))
      else if b =? 2 then
        if k =? 0 then Some (stA 5 0 (c - 1))
        else Some (stOdd 2 0 0 (k - 1) (c - 1))
      else Some (stA (b - 2) (k + 2) (c - 2))
  | stOdd p k n m c =>
    if n =? 0 then
      if p =? 0 then Some (stETail k m c)
      else if p =? 1 then Some (stETail k m c)
      else if m =? 0 then Some (stA (2 * (p - 2) + 1) 0 (2 * (k + 3) + c))
      else Some (stOdd (p - 2) 0 (k + 3) (m - 1) c)
    else
      if p =? 0 then Some (stOdd 0 (k + 2) (n - 1) m c)
      else Some (stOdd (p - 1) (k + 2) (n - 1) m c)
  | stETail k m c =>
    if m =? 0 then Some (stA (2 * k + c + 7) 0 3)
    else if m =? 1 then Some (stA (2 * (k + 4) + 1) 0 c)
    else Some (stOdd (k + 4) 0 0 (m - 2) c)
  end.

Definition encode_F (s : State) : Q * tape :=
  match s with
  | stA b k c => F_cfg (N.to_nat b) (N.to_nat k) (N.to_nat c)
  | stOdd p k n m c => Odd_cfg (N.to_nat p) (N.to_nat k) (N.to_nat n) (N.to_nat m) (N.to_nat c)
  | stETail k m c => ETail_cfg (N.to_nat k) (N.to_nat m) (N.to_nat c)
  end.

Definition encode (s : State) : Q * tape :=
  mirror_cfg (encode_F s).

Theorem init_reaches_start : c0 -[ tm ]->+ encode start.
Proof.
  unfold c0, tape0, start, encode, encode_F, F_cfg, mirror_cfg, perm_q.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add lpow Str_app Streams.hd Streams.tl].
  run_plus.
Qed.

Ltac split_N_eqb_in H :=
  repeat match type of H with
  | context [?x =? ?y] =>
    let Heq := fresh "Heq" in
    destruct (N.eqb_spec x y) as [Heq | Heq]; subst; try discriminate H
  end.

Theorem step_F_sound (s s' : State) (hnext : next s = Some s') :
  encode_F s -[ tm_aux ]->+ encode_F s'.
Proof.
  destruct s as [b k c | p k n m c | k m c]; unfold next in hnext;
    split_N_eqb_in hnext; inversion hnext; subst s'; clear hnext; unfold encode_F.
  - apply_rule rule_F_b0_k0_c0.
  - apply_rule rule_F_b1_k0_c0.
  - apply_rule rule_F_b2_k0_c0.
  - apply_rule rule_F_b3_k0_c0.
  - apply_rule (rule_F_b5_k0_c0 (N.to_nat (b - 5))).
  - apply_rule (rule_F_ksucc_c0 (N.to_nat b) (N.to_nat (k - 1))).
  - apply_rule (rule_F_b0_c1 (N.to_nat k)).
  - apply_rule (rule_F_b1_c1 (N.to_nat k)).
  - apply_rule (rule_F_b2_k0_c1 0%nat).
  - apply_rule (rule_F_b2_ksucc_c1 (N.to_nat (k - 1)) 0%nat).
  - apply_rule (rule_F_b3_c1 (N.to_nat k)).
  - apply_rule (rule_F_b5_c1 (N.to_nat (b - 5)) (N.to_nat k)).
  - apply_rule (rule_F_b0_c2 (N.to_nat k) (N.to_nat (c - 2))).
  - apply_rule (rule_F_b1_c2 (N.to_nat k) (N.to_nat (c - 2))).
  - apply_rule (rule_F_b2_k0_c1 (N.to_nat (c - 1))).
  - apply_rule (rule_F_b2_ksucc_c1 (N.to_nat (k - 1)) (N.to_nat (c - 1))).
  - apply_rule (rule_F_b3_c2 (N.to_nat (b - 3)) (N.to_nat k) (N.to_nat (c - 2))).
  - apply_rule (step_Odd_n0_p0 (N.to_nat k) (N.to_nat m) (N.to_nat c)).
  - apply_rule (step_Odd_n0_p1 (N.to_nat k) (N.to_nat m) (N.to_nat c)).
  - apply_rule (step_Odd_n0_p2_m0 (N.to_nat (p - 2)) (N.to_nat k) (N.to_nat c)).
  - apply_rule (step_Odd_n0_p2_msucc (N.to_nat (p - 2)) (N.to_nat k) (N.to_nat (m - 1)) (N.to_nat c)).
  - apply_rule (step_Odd_nsucc_p0 (N.to_nat k) (N.to_nat (n - 1)) (N.to_nat m) (N.to_nat c)).
  - apply_rule (step_Odd_nsucc_psucc (N.to_nat (p - 1)) (N.to_nat k) (N.to_nat (n - 1)) (N.to_nat m) (N.to_nat c)).
  - apply_rule (step_ETail_m0 (N.to_nat k) (N.to_nat c)).
  - apply_rule (step_ETail_m1 (N.to_nat k) (N.to_nat c)).
  - apply_rule (step_ETail_m2 (N.to_nat k) (N.to_nat (m - 2)) (N.to_nat c)).
Qed.

Theorem step_sound {s s' : State} (hnext : next s = Some s') :
  encode s -[ tm ]->+ encode s'.
Proof.
  exact (progress_mirror _ _ (step_F_sound s s' hnext)).
Qed.

(* ========================================================================== *)
(* Orbit Reachability Relations & Arithmetic Helpers on Binary N              *)
(* ========================================================================== *)

Inductive OrbitStar (f : State -> option State) : State -> State -> Prop :=
  | ostar_refl s : OrbitStar f s s
  | ostar_step s1 s2 s3 : f s1 = Some s2 -> OrbitStar f s2 s3 -> OrbitStar f s1 s3.

Inductive OrbitPlus (f : State -> option State) : State -> State -> Prop :=
  | oplus_single s1 s2 : f s1 = Some s2 -> OrbitPlus f s1 s2
  | oplus_step s1 s2 s3 : f s1 = Some s2 -> OrbitPlus f s2 s3 -> OrbitPlus f s1 s3.

Lemma ostar_single {f : State -> option State} {s1 s2 : State}
    (h : f s1 = Some s2) : OrbitStar f s1 s2.
Proof. exact (ostar_step f s1 s2 s2 h (ostar_refl f s2)). Qed.

Lemma ostar_trans {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitStar f s1 s2) (h2 : OrbitStar f s2 s3) : OrbitStar f s1 s3.
Proof.
  induction h1 as [s | a b c hab _ ih].
  - exact h2.
  - exact (ostar_step f a b s3 hab (ih h2)).
Qed.

Lemma oplus_to_star {f : State -> option State} {s1 s2 : State}
    (h : OrbitPlus f s1 s2) : OrbitStar f s1 s2.
Proof.
  induction h as [a b hab | a b c hab _ ih].
  - exact (ostar_single hab).
  - exact (ostar_step f a b c hab ih).
Qed.

Lemma oplus_head {f : State -> option State} {s1 s2 s3 : State}
    (h1 : f s1 = Some s2) (h2 : OrbitStar f s2 s3) : OrbitPlus f s1 s3.
Proof.
  revert s1 h1.
  induction h2 as [s | b b' c hbb' _ ih]; intros s1 h1.
  - exact (oplus_single f s1 s h1).
  - exact (oplus_step f s1 b c h1 (ih b hbb')).
Qed.

Lemma oplus_trans {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitPlus f s1 s2) (h2 : OrbitPlus f s2 s3) : OrbitPlus f s1 s3.
Proof.
  induction h1 as [a b hab | a b c hab _ ih].
  - exact (oplus_step f a b s3 hab h2).
  - exact (oplus_step f a b s3 hab (ih h2)).
Qed.

Lemma oplus_trans_star {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitPlus f s1 s2) (h2 : OrbitStar f s2 s3) : OrbitPlus f s1 s3.
Proof.
  induction h1 as [a b hab | a b c hab _ ih].
  - exact (oplus_head hab h2).
  - exact (oplus_step f a b s3 hab (ih h2)).
Qed.

Lemma ostar_trans_plus {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitStar f s1 s2) (h2 : OrbitPlus f s2 s3) : OrbitPlus f s1 s3.
Proof.
  induction h1 as [s | a b c hab _ ih].
  - exact h2.
  - exact (oplus_step f a b s3 hab (ih h2)).
Qed.

Lemma oplus_two {f : State -> option State} {s1 s2 s3 : State}
    (h1 : f s1 = Some s2) (h2 : f s2 = Some s3) : OrbitPlus f s1 s3.
Proof.
  exact (oplus_step f s1 s2 s3 h1 (oplus_single f s2 s3 h2)).
Qed.

Fixpoint iterOpt (f : State -> option State) (n : nat) (s : State) : option State :=
  match n with
  | O => Some s
  | S n' =>
    match f s with
    | Some s' => iterOpt f n' s'
    | None => None
    end
  end.

Lemma iterOpt_plus (f : State -> option State) (n : nat) (s1 s2 s3 : State) :
  f s1 = Some s2 -> iterOpt f n s2 = Some s3 -> OrbitPlus f s1 s3.
Proof.
  revert s1 s2.
  induction n as [| n ih]; intros s1 s2 hf hit; cbn [iterOpt] in hit.
  - inversion hit; subst s3. exact (oplus_single f s1 s2 hf).
  - destruct (f s2) as [s2' |] eqn:hf2; [| discriminate hit].
    exact (oplus_step f s1 s2 s3 hf (ih s2 s2' hf2 hit)).
Qed.

Lemma iterOpt_S_plus (f : State -> option State) (n : nat) (s1 s3 : State) :
  iterOpt f (S n) s1 = Some s3 -> OrbitPlus f s1 s3.
Proof.
  cbn [iterOpt].
  destruct (f s1) as [s2 |] eqn:hf; [| discriminate].
  exact (iterOpt_plus f n s1 s2 s3 hf).
Qed.

Theorem orbitPlus_sound {s1 s2 : State} (h : OrbitPlus next s1 s2) :
  encode s1 -[ tm ]->+ encode s2.
Proof.
  induction h as [a b hab | a b c hab _ ih].
  - exact (step_sound hab).
  - exact (ptrans (step_sound hab) ih).
Qed.

Lemma N_ind_add1 (P : N -> Prop)
    (h0 : P 0) (hs : forall n : N, P n -> P (n + 1)) :
  forall n : N, P n.
Proof.
  apply N.peano_ind; [exact h0 |].
  intros n ih.
  replace (N.succ n) with (n + 1) by lia.
  exact (hs n ih).
Qed.

Lemma N_le_exists_add (a b : N) (h : a <= b) :
  exists d : N, b = d + a.
Proof. exists (b - a). lia. Qed.

Definition cfg_D1 (a u v : N) : State :=
  if v =? 0 then stA (a - 2) 0 (2 * u + 3)
  else stA a u (v - 1).

Definition cfg_Modd (m u v y z : N) : State :=
  if y =? 0 then cfg_D1 (2 * m + 1) u (v + z)
  else stOdd m u (v / 2) (y - 1) z.

Theorem cfg_Modd_y0_eq_D1 (m u v z : N) :
  cfg_Modd m u v 0 z = cfg_D1 (2 * m + 1) u (v + z).
Proof. reflexivity. Qed.

Ltac split_N_eqb :=
  repeat match goal with
  | |- context [?x =? ?y] =>
    let H := fresh "Heqb" in
    destruct (N.eqb_spec x y) as [H | H]; try lia
  end.

Ltac solve_state_eq :=
  unfold cfg_Modd, cfg_D1;
  split_N_eqb;
  f_equal; lia.

Ltac solve_next :=
  unfold cfg_Modd, cfg_D1, next;
  split_N_eqb;
  f_equal; f_equal; lia.

(* ========================================================================== *)
(* Layer 2b: Drain & Exponential Acceleration Lemmas                          *)
(* ========================================================================== *)

Theorem iter_A_drain (j b k c : N) :
  OrbitStar next (stA (b + 2 * j + 1) k (c + 2 * j)) (stA (b + 1) (k + 2 * j) c).
Proof.
  revert k.
  induction j as [| j ih] using N_ind_add1; intro k.
  - replace (b + 2 * 0 + 1) with (b + 1) by lia.
    replace (c + 2 * 0) with c by lia.
    replace (k + 2 * 0) with k by lia.
    apply ostar_refl.
  - apply (ostar_step next _ (stA (b + 2 * j + 1) (k + 2) (c + 2 * j))); [solve_next |].
    replace (k + 2 * (j + 1)) with ((k + 2) + 2 * j) by lia.
    exact (ih (k + 2)).
Qed.

Theorem drain_D1_v2 (k a u v : N) (hv : 1 <= v) :
  OrbitStar next (cfg_D1 (a + 2 * k + 1) u (v + 2 * k)) (cfg_D1 (a + 1) (u + 2 * k) v).
Proof.
  unfold cfg_D1. split_N_eqb.
  replace (v + 2 * k - 1) with ((v - 1) + 2 * k) by lia.
  exact (iter_A_drain k a u (v - 1)).
Qed.

Theorem drain_D1_a1_v2 (k u v : N) (hv : 1 <= v) :
  OrbitStar next (cfg_D1 1 u (v + 2 * k)) (cfg_D1 1 (u + 2 * k) v).
Proof.
  revert u.
  induction k as [| k ih] using N_ind_add1; intro u.
  - replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ostar_refl.
  - apply (ostar_step next _ (cfg_D1 1 (u + 2) (v + 2 * k))); [solve_next |].
    replace (u + 2 * (k + 1)) with ((u + 2) + 2 * k) by lia.
    exact (ih (u + 2)).
Qed.

Theorem accel_D1_double (a u : N) (ha : 2 <= a) :
  OrbitPlus next (cfg_D1 (a + 2 * u + 7) u 0) (cfg_D1 (a + 1) (2 * u + 4) 0).
Proof.
  assert (h_in : cfg_D1 (a + 2 * u + 7) u 0 =
                 cfg_D1 ((a + 2) + 2 * (u + 1) + 1) 0 (2 + 2 * (u + 1))) by solve_state_eq.
  rewrite h_in.
  pose proof (drain_D1_v2 (u + 1) (a + 2) 0 2 ltac:(lia)) as h1.
  assert (h2 : next (cfg_D1 ((a + 2) + 1) (0 + 2 * (u + 1)) 2) =
               Some (cfg_D1 (a + 1) (2 * u + 4) 0)) by solve_next.
  exact (ostar_trans_plus h1 (oplus_single next _ _ h2)).
Qed.

Theorem rule_Modd_m0_v2 (u v y z : N) (hv : 1 <= v) :
  OrbitPlus next (cfg_Modd 0 u (v + 2) y z) (cfg_Modd 0 (u + 2) v y z).
Proof. apply oplus_single. solve_next. Qed.

Theorem rule_Modd_m1_v2 (m u v y z : N) (hv : 1 <= v) :
  OrbitPlus next (cfg_Modd (m + 1) u (v + 2) y z) (cfg_Modd m (u + 2) v y z).
Proof. apply oplus_single. solve_next. Qed.

Theorem rule_Modd_m2_v1 (m u y z : N) :
  OrbitPlus next (cfg_Modd (m + 2) u 1 (y + 1) z) (cfg_Modd m 0 (2 * u + 7) y z).
Proof. apply oplus_single. solve_next. Qed.

Theorem rule_Modd_m0_v1_y1 (u z : N) :
  OrbitPlus next (cfg_Modd 0 u 1 1 z) (cfg_D1 (2 * u + z + 9) 0 0).
Proof.
  apply (oplus_two (s2 := stETail u 0 z)); solve_next.
Qed.

Theorem rule_Modd_m0_v1_y2 (u y z : N) :
  OrbitPlus next (cfg_Modd 0 u 1 (y + 2) z) (cfg_Modd (u + 4) 0 1 y z).
Proof.
  apply (oplus_two (s2 := stETail u (y + 1) z)); solve_next.
Qed.

Theorem drain_Modd_v2 (k m u v y z : N) (hv : 1 <= v) :
  OrbitStar next (cfg_Modd (m + k) u (v + 2 * k) y z) (cfg_Modd m (u + 2 * k) v y z).
Proof.
  revert m u v hv.
  induction k as [| k ih] using N_ind_add1; intros m u v hv.
  - replace (m + 0) with m by lia.
    replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ostar_refl.
  - replace (m + (k + 1)) with ((m + k) + 1) by lia.
    replace (v + 2 * (k + 1)) with ((v + 2 * k) + 2) by lia.
    pose proof (rule_Modd_m1_v2 (m + k) u (v + 2 * k) y z ltac:(lia)) as h_step.
    pose proof (ih m (u + 2) v hv) as h_ih.
    replace ((u + 2) + 2 * k) with (u + 2 * (k + 1)) in h_ih by lia.
    exact (oplus_to_star (oplus_trans_star h_step h_ih)).
Qed.

Theorem drain_Modd_m0_v2 (k u v y z : N) (hv : 1 <= v) :
  OrbitStar next (cfg_Modd 0 u (v + 2 * k) y z) (cfg_Modd 0 (u + 2 * k) v y z).
Proof.
  revert u v hv.
  induction k as [| k ih] using N_ind_add1; intros u v hv.
  - replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ostar_refl.
  - replace (v + 2 * (k + 1)) with ((v + 2 * k) + 2) by lia.
    pose proof (rule_Modd_m0_v2 u (v + 2 * k) y z ltac:(lia)) as h1.
    pose proof (ih (u + 2) v hv) as h2.
    replace ((u + 2) + 2 * k) with (u + 2 * (k + 1)) in h2 by lia.
    exact (oplus_to_star (oplus_trans_star h1 h2)).
Qed.

Lemma pow2_add (a b : N) : 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. apply N.pow_add_r. Qed.

Lemma pow2_succ (n : N) : 2 ^ (n + 1) = 2 ^ n * 2.
Proof. rewrite N.pow_add_r. change (2 ^ 1) with 2. reflexivity. Qed.

Lemma mul_pow2_ge (k n : N) : k <= k * 2 ^ n.
Proof.
  induction n as [| n ih] using N_ind_add1.
  - change (2 ^ 0) with 1. lia.
  - rewrite pow2_succ. lia.
Qed.

Lemma pow2_mono {a b : N} (h : a <= b) : 2 ^ a <= 2 ^ b.
Proof.
  replace b with (a + (b - a)) by lia.
  rewrite pow2_add.
  apply mul_pow2_ge.
Qed.

Lemma pow2_ge_two_mul (n : N) (hn : 5 <= n) : 2 * n + 6 <= 2 ^ n.
Proof.
  destruct (N_le_exists_add 5 n hn) as [d ->]. clear hn.
  induction d as [| d ih] using N_ind_add1.
  - apply N.leb_le. vm_compute. reflexivity.
  - replace (d + 1 + 5) with ((d + 5) + 1) by lia.
    rewrite pow2_succ. lia.
Qed.

Lemma mul_pow2_ge_linear (u n : N) :
  2 * (u + 4) + 2 * n <= 2 * (u + 4) * 2 ^ n.
Proof.
  induction n as [| n ih] using N_ind_add1.
  - change (2 ^ 0) with 1. lia.
  - pose proof (mul_pow2_ge (u + 4) n) as h1.
    rewrite pow2_succ. nia.
Qed.

Theorem exp_step_D1_exact (n a u : N) (ha : 2 <= a) :
  OrbitStar next
    (cfg_D1 (a + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1) u 0)
    (cfg_D1 (a + 1) ((u + 4) * 2 ^ n - 4) 0).
Proof.
  revert a u ha.
  induction n as [| n ih] using N_ind_add1; intros a u ha.
  - change (2 ^ 0) with 1.
    replace (a + (2 * (u + 4) * 1 - 2 * (u + 4) - 2 * 0) + 1) with (a + 1) by lia.
    replace ((u + 4) * 1 - 4) with u by lia.
    apply ostar_refl.
  - set (k := (u + 4) * 2 ^ n).
    pose proof (mul_pow2_ge (u + 4) n) as hk; fold k in hk.
    pose proof (mul_pow2_ge_linear u n) as hlin.
    assert (h2k : 2 * (u + 4) * 2 ^ n = 2 * k) by (unfold k; lia).
    assert (hpow : 2 * (u + 4) * 2 ^ (n + 1) = 4 * k) by (unfold k; rewrite pow2_succ; lia).
    replace (a + (2 * (u + 4) * 2 ^ (n + 1) - 2 * (u + 4) - 2 * (n + 1)) + 1)
      with ((a + 2 * (k - 4) + 6) + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1) by lia.
    pose proof (ih (a + 2 * (k - 4) + 6) u ltac:(lia)) as h1.
    replace ((a + 2 * (k - 4) + 6) + 1) with (a + 2 * (k - 4) + 7) in h1 by lia.
    pose proof (accel_D1_double a (k - 4) ha) as h2.
    assert (hu_out : 2 * (k - 4) + 4 = (u + 4) * 2 ^ (n + 1) - 4).
    { unfold k in *. rewrite pow2_succ. lia. }
    rewrite hu_out in h2.
    exact (ostar_trans h1 (oplus_to_star h2)).
Qed.

Theorem enter_Modd_from_D1 (k u z : N)
    (hk : 1 <= k) (hz : 2 * u + 2 = 2 * k + z) :
  OrbitPlus next (cfg_D1 (2 * k + 4) u 0) (cfg_Modd 2 0 1 (2 * k) z).
Proof.
  assert (h_in : cfg_D1 (2 * k + 4) u 0 = cfg_D1 (1 + 2 * k + 1) 0 ((z + 2) + 2 * k))
    by solve_state_eq.
  rewrite h_in.
  pose proof (drain_D1_v2 k 1 0 (z + 2) ltac:(lia)) as h1.
  assert (h_step : next (cfg_D1 (1 + 1) (0 + 2 * k) (z + 2)) = Some (cfg_Modd 2 0 1 (2 * k) z))
    by solve_next.
  exact (ostar_trans_plus h1 (oplus_single next _ _ h_step)).
Qed.

Theorem accel_Modd_double (m u y z : N) :
  OrbitPlus next (cfg_Modd (m + u + 5) u 1 (y + 1) z) (cfg_Modd m (2 * u + 6) 1 y z).
Proof.
  replace (m + u + 5) with ((m + (u + 3)) + 2) by lia.
  pose proof (rule_Modd_m2_v1 (m + (u + 3)) u y z) as h1.
  replace (2 * u + 7) with (1 + 2 * (u + 3)) in h1 by lia.
  pose proof (drain_Modd_v2 (u + 3) m 0 1 y z ltac:(lia)) as h2.
  replace (0 + 2 * (u + 3)) with (2 * u + 6) in h2 by lia.
  exact (oplus_trans_star h1 h2).
Qed.

Lemma six_pow2_ge_linear (e : N) : e + 6 <= 6 * 2 ^ e.
Proof.
  induction e as [| e ih] using N_ind_add1.
  - change (2 ^ 0) with 1. lia.
  - rewrite pow2_succ. lia.
Qed.

Theorem exp_step_Modd_exact (e m y z : N) :
  OrbitStar next
    (cfg_Modd (m + (6 * 2 ^ e - 6 - e)) 0 1 (y + e) z)
    (cfg_Modd m (6 * 2 ^ e - 6) 1 y z).
Proof.
  revert m y.
  induction e as [| e ih] using N_ind_add1; intros m y.
  - change (2 ^ 0) with 1.
    replace (m + (6 * 1 - 6 - 0)) with m by lia.
    replace (y + 0) with y by lia.
    replace (6 * 1 - 6) with 0 by lia.
    apply ostar_refl.
  - set (k := 6 * 2 ^ e).
    pose proof (six_pow2_ge_linear e) as hk; fold k in hk.
    assert (hpow : 6 * 2 ^ (e + 1) = k + k) by (unfold k; rewrite pow2_succ; lia).
    replace (m + (6 * 2 ^ (e + 1) - 6 - (e + 1)))
      with ((m + (k - 6) + 5) + (6 * 2 ^ e - 6 - e)) by (fold k; lia).
    replace (y + (e + 1)) with ((y + 1) + e) by lia.
    pose proof (ih (m + (k - 6) + 5) (y + 1)) as h1.
    fold k in h1.
    pose proof (accel_Modd_double m (k - 6) y z) as h2.
    replace (2 * (k - 6) + 6) with (6 * 2 ^ (e + 1) - 6) in h2 by lia.
    exact (ostar_trans h1 (oplus_to_star h2)).
Qed.

Theorem finish_pass_Modd (m u y z : N) (hm : m <= u + 3) :
  OrbitPlus next (cfg_Modd (m + 2) u 1 (y + 3) z) (cfg_Modd (2 * u + 10) 0 1 y z).
Proof.
  replace (y + 3) with ((y + 2) + 1) by lia.
  pose proof (rule_Modd_m2_v1 m u (y + 2) z) as h1.
  pose proof (drain_Modd_v2 m 0 0 (1 + 2 * (u + 3 - m)) (y + 2) z ltac:(lia)) as h2.
  replace (0 + m) with m in h2 by lia.
  replace ((1 + 2 * (u + 3 - m)) + 2 * m) with (2 * u + 7) in h2 by lia.
  pose proof (oplus_trans_star h1 h2) as h12.
  pose proof (drain_Modd_m0_v2 (u + 3 - m) (0 + 2 * m) 1 (y + 2) z ltac:(lia)) as h3.
  pose proof (oplus_trans_star h12 h3) as h123.
  replace (0 + 2 * m + 2 * (u + 3 - m)) with (2 * u + 6) in h123 by lia.
  pose proof (rule_Modd_m0_v1_y2 (2 * u + 6) y z) as h4.
  replace ((2 * u + 6) + 4) with (2 * u + 10) in h4 by lia.
  exact (oplus_trans h123 h4).
Qed.

Theorem finish_exit_Modd_y2 (m u z : N) (hm : m <= u + 3) :
  OrbitPlus next (cfg_Modd (m + 2) u 1 2 z) (cfg_D1 (4 * u + z + 21) 0 0).
Proof.
  replace 2 with (1 + 1) at 2 by lia.
  pose proof (rule_Modd_m2_v1 m u 1 z) as h1.
  pose proof (drain_Modd_v2 m 0 0 (1 + 2 * (u + 3 - m)) 1 z ltac:(lia)) as h2.
  replace (0 + m) with m in h2 by lia.
  replace ((1 + 2 * (u + 3 - m)) + 2 * m) with (2 * u + 7) in h2 by lia.
  pose proof (oplus_trans_star h1 h2) as h12.
  pose proof (drain_Modd_m0_v2 (u + 3 - m) (0 + 2 * m) 1 1 z ltac:(lia)) as h3.
  pose proof (oplus_trans_star h12 h3) as h123.
  replace (0 + 2 * m + 2 * (u + 3 - m)) with (2 * u + 6) in h123 by lia.
  pose proof (rule_Modd_m0_v1_y1 (2 * u + 6) z) as h4.
  replace (2 * (2 * u + 6) + z + 9) with (4 * u + z + 21) in h4 by lia.
  exact (oplus_trans h123 h4).
Qed.

Theorem pass0_Modd (y z : N) :
  OrbitPlus next (cfg_Modd 2 0 1 (y + 3) z) (cfg_Modd 10 0 1 y z).
Proof.
  exact (finish_pass_Modd 0 0 y z ltac:(lia)).
Qed.

Theorem single_pass_Modd_pos (e y z : N) :
  OrbitPlus next
    (cfg_Modd (6 * 2 ^ e - 2) 0 1 (y + e + 3) z)
    (cfg_Modd (6 * 2 ^ (e + 1) - 2) 0 1 y z).
Proof.
  pose proof (six_pow2_ge_linear e) as hk.
  pose proof (exp_step_Modd_exact e (e + 4) (y + 3) z) as h1.
  replace ((e + 4) + (6 * 2 ^ e - 6 - e)) with (6 * 2 ^ e - 2) in h1 by lia.
  replace ((y + 3) + e) with (y + e + 3) in h1 by lia.
  replace (e + 4) with ((e + 2) + 2) in h1 by lia.
  pose proof (finish_pass_Modd (e + 2) (6 * 2 ^ e - 6) y z ltac:(lia)) as h2.
  assert (hu_out : 2 * (6 * 2 ^ e - 6) + 10 = 6 * 2 ^ (e + 1) - 2).
  { rewrite pow2_succ. lia. }
  rewrite hu_out in h2.
  exact (ostar_trans_plus h1 h2).
Qed.

Lemma tri_succ (e : N) :
  (e + 1) * (e + 6) / 2 = e * (e + 5) / 2 + (e + 3).
Proof.
  assert (h : (e + 1) * (e + 6) = e * (e + 5) + 2 * (e + 3)) by nia.
  rewrite h. lia.
Qed.

Lemma two_mul_tri (E : N) : 2 * (E * (E + 5) / 2) = E * (E + 5).
Proof.
  induction E as [| e ih] using N_ind_add1.
  - vm_compute. reflexivity.
  - replace (e + 1 + 5) with (e + 6) by lia.
    rewrite tri_succ. nia.
Qed.

Theorem multi_pass_Modd_pos (E y z : N) (hE : 1 <= E) :
  OrbitPlus next
    (cfg_Modd 2 0 1 (y + E * (E + 5) / 2) z)
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z).
Proof.
  destruct (N_le_exists_add 1 E hE) as [d ->]. clear hE.
  revert y.
  induction d as [| d ih] using N_ind_add1; intro y.
  - replace (0 + 1) with 1 by lia.
    replace (y + 1 * (1 + 5) / 2) with (y + 3) by (change (1 * (1 + 5) / 2) with 3; lia).
    change (6 * 2 ^ 1 - 2) with 10.
    exact (pass0_Modd y z).
  - pose proof (tri_succ (d + 1)) as htri.
    replace (d + 1 + 1 + 5) with (d + 1 + 6) by lia.
    replace (y + (d + 1 + 1) * (d + 1 + 6) / 2)
      with ((y + (d + 1) + 3) + (d + 1) * (d + 1 + 5) / 2) by lia.
    pose proof (ih (y + (d + 1) + 3)) as h1.
    pose proof (single_pass_Modd_pos (d + 1) y z) as h2.
    exact (oplus_trans h1 h2).
Qed.

Theorem exit_Modd_y1 (E z : N) :
  OrbitPlus next
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 1 z)
    (cfg_D1 (12 * 2 ^ E - 7) 0 (z + 7)).
Proof.
  pose proof (six_pow2_ge_linear E) as hk.
  replace (6 * 2 ^ E - 2) with ((6 * 2 ^ E - 4) + 2) by lia.
  replace 1 with (0 + 1) at 2 by lia.
  pose proof (rule_Modd_m2_v1 (6 * 2 ^ E - 4) 0 0 z) as h1.
  rewrite cfg_Modd_y0_eq_D1 in h1.
  replace (2 * (6 * 2 ^ E - 4) + 1) with (12 * 2 ^ E - 7) in h1 by lia.
  replace (2 * 0 + 7 + z) with (z + 7) in h1 by lia.
  exact h1.
Qed.

Theorem exit_Modd_mid (E y z : N) (hy1 : 2 <= y) (hy2 : y <= E + 1) :
  OrbitPlus next
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z)
    (cfg_D1 (12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3) 0 (12 * 2 ^ (y - 1) + z - 5)).
Proof.
  set (r := y - 1).
  assert (hrE : r <= E) by (unfold r; lia).
  pose proof (pow2_mono hrE) as hpow_ge.
  pose proof (six_pow2_ge_linear r) as hlin_r.
  set (m_rem := 6 * 2 ^ E - 6 * 2 ^ r + r + 4).
  pose proof (exp_step_Modd_exact r m_rem 1 z) as h1.
  replace (m_rem + (6 * 2 ^ r - 6 - r)) with (6 * 2 ^ E - 2) in h1 by (unfold m_rem, r in *; lia).
  replace (1 + r) with y in h1 by (unfold r; lia).
  replace m_rem with ((m_rem - 2) + 2) in h1 by (unfold m_rem, r in *; lia).
  replace 1 with (0 + 1) in h1 at 3 by lia.
  pose proof (rule_Modd_m2_v1 (m_rem - 2) (6 * 2 ^ r - 6) 0 z) as h2.
  rewrite cfg_Modd_y0_eq_D1 in h2.
  replace (2 * (m_rem - 2) + 1) with (12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3) in h2
    by (unfold m_rem, r in *; lia).
  replace (2 * (6 * 2 ^ r - 6) + 7 + z) with (12 * 2 ^ (y - 1) + z - 5) in h2
    by (unfold r in *; lia).
  exact (ostar_trans_plus h1 h2).
Qed.

Theorem exit_Modd_yE2 (E z : N) :
  OrbitPlus next
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 (E + 2) z)
    (cfg_D1 (12 * 2 ^ (E + 1) + z - 3) 0 0).
Proof.
  pose proof (six_pow2_ge_linear E) as hk.
  pose proof (exp_step_Modd_exact E (E + 4) 2 z) as h1.
  replace ((E + 4) + (6 * 2 ^ E - 6 - E)) with (6 * 2 ^ E - 2) in h1 by lia.
  replace (2 + E) with (E + 2) in h1 by lia.
  replace (E + 4) with ((E + 2) + 2) in h1 by lia.
  pose proof (finish_exit_Modd_y2 (E + 2) (6 * 2 ^ E - 6) z ltac:(lia)) as h2.
  assert (ha_out : 4 * (6 * 2 ^ E - 6) + z + 21 = 12 * 2 ^ (E + 1) + z - 3).
  { rewrite pow2_succ. lia. }
  rewrite ha_out in h2.
  exact (ostar_trans_plus h1 h2).
Qed.

Theorem odd_v1_ge_a1_reload (m kv : N) (h : m <= kv) :
  OrbitPlus next (cfg_D1 (2 * m + 1) 0 (2 * kv + 1)) (cfg_D1 (4 * kv + 8) 0 0).
Proof.
  pose proof (drain_D1_v2 m 0 0 (1 + 2 * (kv - m)) ltac:(lia)) as h1.
  replace (0 + 2 * m + 1) with (2 * m + 1) in h1 by lia.
  replace ((1 + 2 * (kv - m)) + 2 * m) with (2 * kv + 1) in h1 by lia.
  replace (0 + 1) with 1 in h1 by lia.
  pose proof (drain_D1_a1_v2 (kv - m) (0 + 2 * m) 1 ltac:(lia)) as h2.
  pose proof (ostar_trans h1 h2) as h12.
  replace (0 + 2 * m + 2 * (kv - m)) with (2 * kv) in h12 by lia.
  assert (h3 : OrbitPlus next (cfg_D1 1 (2 * kv) 1) (cfg_D1 (4 * kv + 8) 0 0)).
  { destruct (N.eqb_spec kv 0) as [-> | hkv].
    - apply oplus_single. solve_next.
    - apply (oplus_two (s2 := stA 1 (2 * kv - 1) 1)); solve_next. }
  exact (ostar_trans_plus h12 h3).
Qed.

Theorem odd_drain_v1 (ma kv : N) (hma : 1 <= ma) :
  OrbitPlus next
    (cfg_D1 (2 * ma + 2 * kv + 3) 0 (2 * kv + 1))
    (cfg_D1 (2 * ma + 1) (2 * kv + 1) 0).
Proof.
  pose proof (drain_D1_v2 kv (2 * ma + 2) 0 1 ltac:(lia)) as h1.
  replace ((2 * ma + 2) + 2 * kv + 1) with (2 * ma + 2 * kv + 3) in h1 by lia.
  replace (1 + 2 * kv) with (2 * kv + 1) in h1 by lia.
  replace ((2 * ma + 2) + 1) with (2 * ma + 3) in h1 by lia.
  replace (0 + 2 * kv) with (2 * kv) in h1 by lia.
  assert (h2 : OrbitPlus next (cfg_D1 (2 * ma + 3) (2 * kv) 1)
                              (cfg_D1 (2 * ma + 1) (2 * kv + 1) 0)).
  { destruct (N.eqb_spec kv 0) as [-> | hkv].
    - apply oplus_single. solve_next.
    - apply (oplus_two (s2 := stA (2 * ma + 3) (2 * kv - 1) 1)); solve_next. }
  exact (ostar_trans_plus h1 h2).
Qed.

Theorem odd_rem_ge3_reload (m u : N) (hm : m <= u + 2) :
  OrbitPlus next (cfg_D1 (2 * m + 3) u 0) (cfg_D1 (4 * u + 14) 0 0).
Proof.
  assert (h_in : cfg_D1 (2 * m + 3) u 0 = cfg_D1 (2 * m + 1) 0 (2 * u + 4)) by solve_state_eq.
  rewrite h_in.
  destruct (N.eqb_spec m (u + 2)) as [-> | hm1].
  - pose proof (drain_D1_v2 (u + 1) 2 0 2 ltac:(lia)) as h1.
    replace (2 + 2 * (u + 1) + 1) with (2 * (u + 2) + 1) in h1 by lia.
    replace (2 + 2 * (u + 1)) with (2 * u + 4) in h1 by lia.
    replace (2 + 1) with 3 in h1 by lia.
    replace (0 + 2 * (u + 1)) with (2 * u + 2) in h1 by lia.
    assert (h2 : next (cfg_D1 3 (2 * u + 2) 2) = Some (cfg_D1 (4 * u + 14) 0 0)) by solve_next.
    exact (ostar_trans_plus h1 (oplus_single next _ _ h2)).
  - assert (hm_le : m <= u + 1) by lia.
    pose proof (drain_D1_v2 m 0 0 (2 + 2 * (u + 1 - m)) ltac:(lia)) as h1.
    replace (0 + 2 * m + 1) with (2 * m + 1) in h1 by lia.
    replace ((2 + 2 * (u + 1 - m)) + 2 * m) with (2 * u + 4) in h1 by lia.
    replace (0 + 1) with 1 in h1 by lia.
    pose proof (drain_D1_a1_v2 (u + 1 - m) (0 + 2 * m) 2 ltac:(lia)) as h2.
    pose proof (ostar_trans h1 h2) as h12.
    replace (0 + 2 * m + 2 * (u + 1 - m)) with (2 * u + 2) in h12 by lia.
    assert (h3 : next (cfg_D1 1 (2 * u + 2) 2) = Some (cfg_D1 (4 * u + 14) 0 0)) by solve_next.
    exact (ostar_trans_plus h12 (oplus_single next _ _ h3)).
Qed.

(* ========================================================================== *)
(* Layer 3: Era-Step Templates, Initial 7 Eras, and Inductive Tower Step      *)
(* ========================================================================== *)

Theorem era_mid_ge3_step (a0 n k0 z E y ma kv r m_rem2 A_next : N)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : 1 <= k0)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : 1 <= E)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * y)
    (hy1 : 2 <= y)
    (hy2 : y <= E + 1)
    (ha1 : 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3 = 2 * ma + 2 * kv + 3)
    (hv1 : 12 * 2 ^ (y - 1) + z - 5 = 2 * kv + 1)
    (ha2 : 2 * ma + 1 = (2 * m_rem2 + 2) + (2 * (2 * kv + 5) * 2 ^ r - 2 * (2 * kv + 5) - 2 * r) + 1)
    (hm2 : m_rem2 <= (2 * kv + 5) * 2 ^ r - 2)
    (hAnext : A_next = 4 * ((2 * kv + 5) * 2 ^ r - 4) + 14) :
  OrbitPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(clear; lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by (clear; lia).
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by (clear; lia).
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ostar_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  replace (2 * k0) with (y + E * (E + 5) / 2) in h12
    by (generalize (E * (E + 5) / 2) (E * (E + 5)) hy0 htri; clear; intros; lia).
  pose proof (multi_pass_Modd_pos E y z hE) as h3.
  pose proof (oplus_trans h12 h3) as h123.
  pose proof (exit_Modd_mid E y z hy1 hy2) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (oplus_trans h123 h4) as h1234.
  assert (hma : 1 <= ma)
    by (generalize (2 * (2 * kv + 5) * 2 ^ r - 2 * (2 * kv + 5) - 2 * r) ha2; clear; intros; lia).
  pose proof (odd_drain_v1 ma kv hma) as h5.
  pose proof (oplus_trans h1234 h5) as h12345.
  rewrite ha2 in h12345.
  pose proof (exp_step_D1_exact r (2 * m_rem2 + 2) (2 * kv + 1) ltac:(clear; lia)) as h6.
  replace (2 * kv + 1 + 4) with (2 * kv + 5) in h6 by (clear; lia).
  replace ((2 * m_rem2 + 2) + 1) with (2 * m_rem2 + 3) in h6 by (clear; lia).
  pose proof (oplus_trans_star h12345 h6) as h123456.
  pose proof (mul_pow2_ge (2 * kv + 5) r) as hpow_r.
  pose proof (odd_rem_ge3_reload m_rem2 ((2 * kv + 5) * 2 ^ r - 4)
                ltac:(clear - hm2 hpow_r; lia)) as h7.
  rewrite <- hAnext in h7.
  exact (oplus_trans h123456 h7).
Qed.

Theorem era_yE2_ge3_step (a0 n k0 z E r m_rem2 A_next : N)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : 1 <= k0)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : 1 <= E)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * (E + 2))
    (ha1 : 12 * 2 ^ (E + 1) + z - 3 = (2 * m_rem2 + 2) + (8 * 2 ^ r - 8 - 2 * r) + 1)
    (hm2 : m_rem2 <= 4 * 2 ^ r - 2)
    (hAnext : A_next = 4 * (4 * 2 ^ r - 4) + 14) :
  OrbitPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(clear; lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by (clear; lia).
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by (clear; lia).
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ostar_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  replace (2 * k0) with ((E + 2) + E * (E + 5) / 2) in h12
    by (generalize (E * (E + 5) / 2) (E * (E + 5)) hy0 htri; clear; intros; lia).
  pose proof (multi_pass_Modd_pos E (E + 2) z hE) as h3.
  pose proof (oplus_trans h12 h3) as h123.
  pose proof (exit_Modd_yE2 E z) as h4.
  rewrite ha1 in h4.
  pose proof (oplus_trans h123 h4) as h1234.
  pose proof (exp_step_D1_exact r (2 * m_rem2 + 2) 0 ltac:(clear; lia)) as h5.
  replace (0 + 4) with 4 in h5 by (clear; lia).
  replace ((2 * m_rem2 + 2) + 1) with (2 * m_rem2 + 3) in h5 by (clear; lia).
  pose proof (oplus_trans_star h1234 h5) as h12345.
  pose proof (mul_pow2_ge 4 r) as hpow_r.
  pose proof (odd_rem_ge3_reload m_rem2 (4 * 2 ^ r - 4)
                ltac:(clear - hm2 hpow_r; lia)) as h6.
  rewrite <- hAnext in h6.
  exact (oplus_trans h12345 h6).
Qed.

Theorem era_mid_v1_ge_a1_step (a0 n k0 z E y m kv A_next : N)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : 1 <= k0)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : 1 <= E)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2 * y)
    (hy1 : 2 <= y)
    (hy2 : y <= E + 1)
    (ha1 : 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3 = 2 * m + 1)
    (hv1 : 12 * 2 ^ (y - 1) + z - 5 = 2 * kv + 1)
    (hm : m <= kv)
    (hAnext : A_next = 4 * kv + 8) :
  OrbitPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(clear; lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by (clear; lia).
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by (clear; lia).
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ostar_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  replace (2 * k0) with (y + E * (E + 5) / 2) in h12
    by (generalize (E * (E + 5) / 2) (E * (E + 5)) hy0 htri; clear; intros; lia).
  pose proof (multi_pass_Modd_pos E y z hE) as h3.
  pose proof (oplus_trans h12 h3) as h123.
  pose proof (exit_Modd_mid E y z hy1 hy2) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (oplus_trans h123 h4) as h1234.
  pose proof (odd_v1_ge_a1_reload m kv hm) as h5.
  rewrite <- hAnext in h5.
  exact (oplus_trans h1234 h5).
Qed.

Theorem era_y1_v1_ge_a1_step (a0 n k0 z E m kv A_next : N)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : 1 <= k0)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : 1 <= E)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2)
    (ha1 : 12 * 2 ^ E - 7 = 2 * m + 1)
    (hv1 : z + 7 = 2 * kv + 1)
    (hm : m <= kv)
    (hAnext : A_next = 4 * kv + 8) :
  OrbitPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(clear; lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by (clear; lia).
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by (clear; lia).
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ostar_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  replace (2 * k0) with (1 + E * (E + 5) / 2) in h12
    by (generalize (E * (E + 5) / 2) (E * (E + 5)) hy0 htri; clear; intros; lia).
  pose proof (multi_pass_Modd_pos E 1 z hE) as h3.
  pose proof (oplus_trans h12 h3) as h123.
  pose proof (exit_Modd_y1 E z) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (oplus_trans h123 h4) as h1234.
  pose proof (odd_v1_ge_a1_reload m kv hm) as h5.
  rewrite <- hAnext in h5.
  exact (oplus_trans h1234 h5).
Qed.

Ltac check_N :=
  (apply N.leb_le; vm_compute; reflexivity) || (vm_compute; reflexivity).

Theorem era0 : OrbitPlus next start (cfg_D1 30 0 0).
Proof.
  apply (iterOpt_S_plus next 15).
  vm_compute. reflexivity.
Qed.

Theorem era1 : OrbitPlus next (cfg_D1 30 0 0) (cfg_D1 126 0 0).
Proof.
  apply (era_yE2_ge3_step 30 2 3 20 1 3 6 126); check_N.
Qed.

Theorem era2 : OrbitPlus next (cfg_D1 126 0 0) (cfg_D1 316 0 0).
Proof.
  apply (era_mid_v1_ge_a1_step 126 4 5 112 2 3 4 77 316); check_N.
Qed.

Theorem era3 : OrbitPlus next (cfg_D1 316 0 0) (cfg_D1 16382 0 0).
Proof.
  apply (era_yE2_ge3_step 316 5 37 176 9 10 2147 16382); check_N.
Qed.

Theorem era4 : OrbitPlus next (cfg_D1 16382 0 0) (cfg_D1 32766 0 0).
Proof.
  apply (era_yE2_ge3_step 16382 11 12 16354 4 11 189 32766); check_N.
Qed.

Theorem era5 : OrbitPlus next (cfg_D1 32766 0 0) (cfg_D1 65492 0 0).
Proof.
  apply (era_y1_v1_ge_a1_step 32766 12 13 32736 5 188 16371 65492); check_N.
Qed.

Definition cfg_Tower (M k : N) : State :=
  cfg_D1 (12 * 2 ^ (2 * M - 3) + 2 * k * 2 ^ M - 2) 0 0.

Definition TowerInv (M k : N) : Prop :=
  128 <= M /\ 4 <= k /\ 3 * M <= k * k /\ 4 * (k * k) <= 2 ^ (M - 2).

Theorem era6 : OrbitPlus next (cfg_D1 65492 0 0) (cfg_Tower 128 9216).
Proof.
  unfold cfg_Tower.
  apply (era_mid_ge3_step 65492 12 16376 10 253 115
    (6 * 2 ^ 253 - 12 * 2 ^ 114 + 113)
    (6 * 2 ^ 114 + 2)
    137
    (3 * 2 ^ 253 - 8 * 2 ^ 137 - 174224571863520493293247799005065324265214)
    (12 * 2 ^ (2 * 128 - 3) + 2 * 9216 * 2 ^ 128 - 2)); check_N.
Qed.

Theorem start_reaches_tower : OrbitPlus next start (cfg_Tower 128 9216).
Proof.
  exact (oplus_trans
    (oplus_trans
      (oplus_trans
        (oplus_trans
          (oplus_trans (oplus_trans era0 era1) era2)
          era3)
        era4)
      era5)
    era6).
Qed.

Theorem tower_inv_init : TowerInv 128 9216.
Proof.
  unfold TowerInv. repeat split; check_N.
Qed.

Lemma sq_sub3_add2 (a0 : N) (hA : 3 <= a0) :
  (a0 - 3) * (a0 + 2) + a0 + 6 = a0 * a0.
Proof. nia. Qed.

Lemma four_mul_assoc (a b c : N) :
  4 * (a * (b * c)) = 2 * (a * b) * (c * 2).
Proof. nia. Qed.

Theorem tower_step_core
    (M k K2 P KP P2 n k0 kz z E y Qv r R QR KZR kv ma m_rem2 M' g k' a0 A_next : N)
    (hM : 128 <= M) (hk : 4 <= k) (h3M : 3 * M <= k * k) (h4k2 : 4 * (k * k) <= 2 ^ (M - 2))
    (hK2_def : K2 = k * k)
    (hP_def : P = 2 ^ (M - 2))
    (hKP_def : KP = k * P)
    (hP2_def : P2 = P * P)
    (hn_def : n = 2 * M - 3)
    (hk0_def : k0 = 4 * P2 + 4 * KP + 2 * M - 2)
    (hkz_def : kz = 4 * P2 - 4 * KP - 2 * M - 1)
    (hz_def : z = 2 * kz)
    (hE_def : E = 4 * P + 2 * k - 3)
    (hy_def : y = 2 * P - 2 * K2 + k + 4 * M - 1)
    (hQ_def : Qv = 2 ^ (y - 1))
    (hr_def : r = E - 1 - y)
    (hR_def : R = 2 ^ r)
    (hQR_def : QR = Qv * R)
    (hKZR_def : KZR = (2 * kz - 1) * R)
    (hkv_def : kv = 6 * Qv + kz - 3)
    (hma_def : ma = 24 * QR - 12 * Qv - kz + y + 3)
    (hm_rem2_def : m_rem2 = 12 * QR - KZR + kz + E)
    (hM'_def : M' = 2 * P + k)
    (hg_def : g = 2 * K2 - 4 * M - 1)
    (hk'_def : k' = (z - 1) * 2 ^ (g - 1))
    (hA_def : a0 = 12 * 2 ^ (2 * M - 3) + 2 * k * 2 ^ M - 2)
    (hAnext_def : A_next = 12 * 2 ^ (2 * M' - 3) + 2 * k' * 2 ^ M' - 2) :
  OrbitPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) /\ TowerInv M' k'.
Proof.
  assert (hK2_ge_3M : 3 * M <= K2) by (rewrite hK2_def; exact h3M).
  assert (hK2_ge_4k : 4 * k <= K2) by (clear - hk hK2_def; nia).
  assert (hP_ge_4K2 : 4 * K2 <= P) by (rewrite hK2_def, hP_def; exact h4k2).
  assert (hP_lin : 2 * (M - 2) + 6 <= P).
  { rewrite hP_def. apply pow2_ge_two_mul. clear - hM; lia. }
  assert (hP_pos : 1 <= P) by (clear - hP_lin; lia).
  assert (hKP_ge_4P : 4 * P <= KP) by (clear - hk hKP_def; nia).
  assert (hP_ge_16k : 16 * k <= P) by (clear - hK2_ge_4k hP_ge_4K2; lia).
  assert (hP2_ge_16KP : 16 * KP <= P2) by (clear - hP_ge_16k hKP_def hP2_def; nia).
  assert (h2M : 2 ^ M = 4 * P).
  { replace M with ((M - 2) + 2) at 1 by (clear - hM; lia).
    rewrite pow2_add, <- hP_def. change (2 ^ 2) with 4. clear; lia. }
  assert (h2k2M : 2 * k * 2 ^ M = 8 * KP) by (rewrite h2M, hKP_def; clear; nia).
  assert (h2M3 : 2 ^ (2 * M - 3) = 2 * P2).
  { replace (2 * M - 3) with ((M - 2) + (M - 2) + 1) by (clear - hM; lia).
    rewrite !pow2_add, <- hP_def, <- hP2_def. change (2 ^ 1) with 2. clear; lia. }
  assert (hy_ge_P : P + 4 * M - 1 <= y) by (clear - hM hk hP_ge_4K2 hy_def; lia).
  assert (hy_le_E : y + 1 <= E) by (clear - hM hk hK2_ge_3M hP_ge_4K2 hE_def hy_def; lia).
  assert (hQR : 2 ^ E = 4 * QR).
  { replace E with ((y - 1) + r + 2) at 1 by (clear - hM hy_ge_P hy_le_E hr_def; lia).
    rewrite !pow2_add, <- hQ_def, <- hR_def, <- hQR_def. change (2 ^ 2) with 4. clear; nia. }
  assert (hQ_ge_16P2 : 16 * P2 <= Qv).
  { assert (hy_exp : (M - 2) + (M - 2) + 4 <= y - 1) by (clear - hM hP_lin hy_ge_P; lia).
    pose proof (pow2_mono hy_exp) as hmono.
    rewrite !pow2_add, <- hP_def, <- hP2_def, <- hQ_def in hmono.
    change (2 ^ 4) with 16 in hmono. clear - hmono; nia. }
  assert (hQ_pos : 1 <= Qv) by (clear - hP_pos hKP_ge_4P hP2_ge_16KP hQ_ge_16P2; lia).
  assert (hR_ge : 2 * r + 6 <= R).
  { rewrite hR_def. apply pow2_ge_two_mul.
    clear - hM hk hK2_ge_3M hP_ge_4K2 hE_def hy_def hr_def; lia. }
  assert (hQR_ge_2Q : 2 * Qv <= QR) by (clear - hR_ge hQR_def; nia).
  assert (hQR_ge_R : R <= QR) by (clear - hQ_pos hQR_def; nia).
  assert (hkz_pos : 1 <= kz) by (clear - hM hP_lin hKP_ge_4P hP2_ge_16KP hkz_def; lia).
  assert (hkz_ge_E : E + 2 <= kz)
    by (clear - hM hk hP_lin hP_ge_16k hKP_ge_4P hP2_ge_16KP hkz_def hE_def; lia).
  assert (h2kz_le_6Q : 2 * kz - 1 <= 6 * Qv) by (clear - hkz_def hQ_ge_16P2; lia).
  assert (hKZR_ge : 2 * kz - 1 <= KZR)
    by (generalize (2 * kz - 1) hKZR_def; clear - hR_ge; intros; nia).
  assert (h6QR_ge_KZR : KZR <= 6 * QR)
    by (generalize (2 * kz - 1) h2kz_le_6Q hKZR_def; clear - hQR_def; intros; nia).
  assert (hkv5 : 2 * kv + 5 = 12 * Qv + (2 * kz - 1))
    by (clear - hQ_pos hkz_pos hkv_def; lia).
  assert (hkvR : (2 * kv + 5) * R = 12 * QR + KZR)
    by (rewrite hkv5, hQR_def, hKZR_def; generalize (2 * kz - 1); clear; intros; nia).
  split.
  - apply (era_mid_ge3_step a0 n k0 z E y ma kv r m_rem2 A_next).
    + rewrite hA_def, hn_def, h2M3, h2k2M.
      clear - hM hP_lin hKP_ge_4P hP2_ge_16KP hk0_def; lia.
    + clear - hM hk0_def; lia.
    + rewrite hn_def, h2M3.
      clear - hM hP_lin hKP_ge_4P hP2_ge_16KP hk0_def hkz_def hz_def; lia.
    + clear - hk hP_pos hE_def; lia.
    + pose proof (sq_sub3_add2 (4 * P + 2 * k) ltac:(clear - hk; lia)) as hA_sq.
      replace ((4 * P + 2 * k) - 3) with E in hA_sq by (clear - hE_def; lia).
      replace ((4 * P + 2 * k) + 2) with (E + 5) in hA_sq by (clear - hk hE_def; lia).
      assert (hsq : (4 * P + 2 * k) * (4 * P + 2 * k) = 16 * P2 + 16 * KP + 4 * K2)
        by (clear - hK2_def hKP_def hP2_def; nia).
      rewrite hsq in hA_sq.
      generalize (E * (E + 5)) hA_sq; clear - hM hP_ge_4K2 hk0_def hy_def; intros; lia.
    + clear - hM hy_ge_P; lia.
    + clear - hy_le_E; lia.
    + rewrite hQR, <- hQ_def.
      clear - hQR_ge_2Q hQ_pos hkz_pos h2kz_le_6Q hma_def hkv_def; lia.
    + rewrite <- hQ_def.
      clear - hQ_pos hz_def hkv_def; lia.
    + rewrite <- hR_def.
      assert (h2kvR : 2 * (2 * kv + 5) * R = 2 * (12 * QR + KZR)) by (clear - hkvR; lia).
      rewrite h2kvR, hkv5.
      clear - hQR_ge_2Q hQR_ge_R hR_ge hKZR_ge h6QR_ge_KZR hkz_pos h2kz_le_6Q
              hy_le_E hr_def hma_def hm_rem2_def; lia.
    + rewrite <- hR_def, hkvR.
      clear - h6QR_ge_KZR hkz_pos hKZR_ge hkz_ge_E hm_rem2_def; lia.
    + rewrite hAnext_def, <- hR_def, hkvR.
      replace (4 * (12 * QR + KZR - 4) + 14) with (12 * (4 * QR) + 4 * KZR - 2)
        by (clear - hR_ge hQR_ge_R; lia).
      rewrite <- hQR.
      assert (hE_M' : E = 2 * M' - 3) by (clear - hk hE_def hM'_def; lia).
      assert (hr_split : r = (g - 1) + (M' - 1))
        by (clear - hM hk hK2_ge_3M hP_ge_4K2 hE_def hy_def hr_def hM'_def hg_def; lia).
      assert (h4R : 4 * KZR = 2 * k' * 2 ^ M').
      { assert (hpowM' : 2 ^ M' = 2 ^ (M' - 1) * 2).
        { replace M' with ((M' - 1) + 1) at 1 by (clear - hk hM'_def; lia). apply pow2_succ. }
        assert (hpowR : R = 2 ^ (g - 1) * 2 ^ (M' - 1)).
        { rewrite hR_def, hr_split, pow2_add. reflexivity. }
        rewrite hKZR_def, hpowR, hk'_def, hz_def, hpowM'.
        exact (four_mul_assoc (2 * kz - 1) (2 ^ (g - 1)) (2 ^ (M' - 1))). }
      rewrite hE_M', h4R. reflexivity.
  - unfold TowerInv.
    assert (hg_ge : M <= g - 1) by (clear - hM hK2_ge_3M hg_def; lia).
    assert (h2g_ge_M' : M' <= 2 ^ (g - 1)).
    { pose proof (pow2_mono hg_ge) as h1. rewrite h2M in h1.
      clear - hP_ge_16k hM'_def h1; lia. }
    assert (hz1_ge : 3 <= z - 1) by (clear - hk hP_pos hkz_ge_E hE_def hz_def; lia).
    assert (hk'_ge_3M' : 3 * M' <= k')
      by (generalize (z - 1) (2 ^ (g - 1)) hz1_ge h2g_ge_M' hk'_def; clear; intros; nia).
    assert (hk'_sq : 3 * M' <= k' * k')
      by (clear - hk hM'_def hk'_ge_3M'; nia).
    split; [clear - hM hP_lin hM'_def; lia |].
    split; [clear - hk hM'_def hk'_ge_3M'; lia |].
    split; [exact hk'_sq |].
    assert (hz_lt : z - 1 <= 2 ^ (2 * M - 1)).
    { replace (2 * M - 1) with ((2 * M - 3) + 2) by (clear - hM; lia).
      rewrite pow2_add, h2M3. change (2 ^ 2) with 4. clear - hkz_def hz_def; lia. }
    assert (hk'_le : k' <= 2 ^ (2 * K2 - 2)).
    { assert (h1 : k' <= 2 ^ (2 * M - 1) * 2 ^ (g - 1))
        by (generalize (z - 1) (2 ^ (2 * M - 1)) (2 ^ (g - 1)) hz_lt hk'_def; clear; intros; nia).
      rewrite <- pow2_add in h1.
      assert (hexp : (2 * M - 1) + (g - 1) <= 2 * K2 - 2)
        by (clear - hM hK2_ge_3M hg_def; lia).
      exact (N.le_trans _ _ _ h1 (pow2_mono hexp)). }
    assert (h4k'2 : 4 * (k' * k') <= 2 ^ (4 * K2 - 2)).
    { assert (h2 : 4 * (k' * k') <= 2 ^ 2 * (2 ^ (2 * K2 - 2) * 2 ^ (2 * K2 - 2)))
        by (change (2 ^ 2) with 4; generalize (2 ^ (2 * K2 - 2)) hk'_le; clear; intros; nia).
      rewrite <- !pow2_add in h2.
      replace (2 + ((2 * K2 - 2) + (2 * K2 - 2))) with (4 * K2 - 2) in h2
        by (clear - hM hK2_ge_3M; lia).
      exact h2. }
    assert (hexp_M' : 4 * K2 - 2 <= M' - 2) by (clear - hP_ge_4K2 hk hM'_def; lia).
    exact (N.le_trans _ _ _ h4k'2 (pow2_mono hexp_M')).
Qed.

Theorem tower_step (M k : N) (hinv : TowerInv M k) :
  exists M' k' : N, OrbitPlus next (cfg_Tower M k) (cfg_Tower M' k') /\ TowerInv M' k'.
Proof.
  destruct hinv as [hM [hk [h3M h4k2]]].
  unfold cfg_Tower.
  set (K2 := k * k).
  set (P := 2 ^ (M - 2)).
  set (KP := k * P).
  set (P2 := P * P).
  set (n := 2 * M - 3).
  set (k0 := 4 * P2 + 4 * KP + 2 * M - 2).
  set (kz := 4 * P2 - 4 * KP - 2 * M - 1).
  set (z := 2 * kz).
  set (E := 4 * P + 2 * k - 3).
  set (y := 2 * P - 2 * K2 + k + 4 * M - 1).
  set (Qv := 2 ^ (y - 1)).
  set (r := E - 1 - y).
  set (R := 2 ^ r).
  set (QR := Qv * R).
  set (KZR := (2 * kz - 1) * R).
  set (kv := 6 * Qv + kz - 3).
  set (ma := 24 * QR - 12 * Qv - kz + y + 3).
  set (m_rem2 := 12 * QR - KZR + kz + E).
  set (M' := 2 * P + k).
  set (g := 2 * K2 - 4 * M - 1).
  set (k' := (z - 1) * 2 ^ (g - 1)).
  set (a0 := 12 * 2 ^ (2 * M - 3) + 2 * k * 2 ^ M - 2).
  set (A_next := 12 * 2 ^ (2 * M' - 3) + 2 * k' * 2 ^ M' - 2).
  exists M', k'.
  exact (tower_step_core
    M k K2 P KP P2 n k0 kz z E y Qv r R QR KZR kv ma m_rem2 M' g k' a0 A_next
    hM hk h3M h4k2
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl eq_refl).
Qed.

Theorem init_reaches_tower : c0 -[ tm ]->+ encode (cfg_Tower 128 9216).
Proof.
  exact (ptrans init_reaches_start (orbitPlus_sound start_reaches_tower)).
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt.
  - exact (progress_evstep tm _ _ init_reaches_tower).
  - apply (progress_nonhalt_cond tm (N * N) (128, 9216)
             (fun '(M, k) => encode (cfg_Tower M k))
             (fun '(M, k) => TowerInv M k)).
    + intros [M k] hinv.
      destruct (tower_step M k hinv) as [M' [k' [hstep hinv']]].
      exists (M', k').
      exact (conj (orbitPlus_sound hstep) hinv').
    + exact tower_inv_init.
Qed.
