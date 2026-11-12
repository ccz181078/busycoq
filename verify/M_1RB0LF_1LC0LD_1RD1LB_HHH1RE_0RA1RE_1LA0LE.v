(* 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE (BB(6) holdout #56) never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Lia ZifyNat ZifyN NArith PArith PeanoNat String.
Import ListNotations.

Set Default Goal Selector "!".

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition tm : TM := TM_from_str "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE".
Arguments tm _ : simpl never.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Local Notation "'0inf'" := (const S0).

(* ========================================================================== *)
(* Layer 1: Raw Tape Configurations, Shift Rules, and Macro-Transitions       *)
(* ========================================================================== *)

Close Scope sym_scope.
Open Scope list_scope.
Open Scope nat_scope.

Lemma ptrans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply progress_trans. Qed.

Lemma ps_trans {c1 c2 c3 : Q * tape} : c1 -->+ c2 -> c2 -->* c3 -> c1 -->+ c3.
Proof. apply progress_evstep_trans. Qed.

Lemma sp_trans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->+ c3 -> c1 -->+ c3.
Proof. apply evstep_progress_trans. Qed.

Lemma etrans {c1 c2 c3 : Q * tape} : c1 -->* c2 -> c2 -->* c3 -> c1 -->* c3.
Proof. apply evstep_trans. Qed.

Lemma pev {c1 c2 : Q * tape} : c1 -->+ c2 -> c1 -->* c2.
Proof. apply progress_evstep. Qed.

Ltac fast_simpl_tape :=
  try rewrite move_left_const;
  try rewrite move_right_const;
  cbn [move_left move_right Streams.hd Streams.tl Str_app].

Ltac fast_step :=
  (eapply evstep_step || eapply progress_step);
  [prove_step | fast_simpl_tape].

Ltac fast_finish :=
  (apply evstep_refl'; repeat rewrite <- const_unfold; reflexivity) || finish_progress.

Ltac fast_execute :=
  intros; repeat (try solve [fast_finish]; fast_step).

Ltac fast_start_progress :=
  eapply progress_intro;
  [prove_step | fast_simpl_tape];
  fast_execute.

Lemma lpow_1 {X : Type} (u : list X) : u ^^ 1 = u.
Proof. cbn. apply app_nil_r. Qed.

Lemma lpow_split_r {X : Type} (u : list X) (m n : nat) (r : Stream X) :
  u ^^ (m + n) *> r = u ^^ m *> (u ^^ n *> r).
Proof. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma lpow_succ_r_side {X : Type} (u : list X) (n : nat) (r : Stream X) :
  u ^^ (n + 1) *> r = u *> (u ^^ n *> r).
Proof.
  replace (n + 1) with (1 + n) by lia.
  rewrite lpow_split_r, lpow_1. reflexivity.
Qed.

Lemma lpow_split_l {X : Type} (s : Stream X) (u : list X) (m n : nat) :
  s <* u ^^ (m + n) = (s <* u ^^ m) <* u ^^ n.
Proof.
  rewrite Nat.add_comm, lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma lpow_one_r_side {X : Type} (u : list X) (k : nat) (r : Stream X) :
  u ^^ k *> (u *> r) = u ^^ (k + 1) *> r.
Proof.
  rewrite (lpow_split_r u k 1 r), lpow_1. reflexivity.
Qed.

Lemma lpow_one_l_side {X : Type} (l : Stream X) (u : list X) (k : nat) :
  (l <* u) <* u ^^ k = l <* u ^^ (k + 1).
Proof.
  replace (k + 1) with (1 + k) by lia.
  rewrite (lpow_split_l l u 1 k), lpow_1. reflexivity.
Qed.

Lemma append_zero_pow_01 (s : Stream sym) (k : nat) :
  (s <* [S0]) <* [S0; S1] ^^ k = (s <* [S1; S0] ^^ k) <* [S0].
Proof.
  induction k as [| k ih]; [reflexivity |].
  cbn [lpow]. rewrite Str_app_assoc, ih. reflexivity.
Qed.

Lemma default_pow_01 (c : nat) :
  0inf <* [S0; S1] ^^ c = (0inf <* [S1; S0] ^^ c) <* [S0].
Proof.
  rewrite const_unfold at 1.
  exact (append_zero_pow_01 0inf c).
Qed.

Lemma append_one_pow_10 (s : Stream sym) (k : nat) :
  (s <* [S1]) <* [S1; S0] ^^ k = (s <* [S0; S1] ^^ k) <* [S1].
Proof.
  induction k as [| k ih]; [reflexivity |].
  cbn [lpow]. rewrite Str_app_assoc, ih. reflexivity.
Qed.

Lemma pow_11_eq_pow_1_mul2 (k : nat) :
  [S1; S1] ^^ k = [S1] ^^ (2 * k).
Proof.
  replace (2 * k) with (k * 2) by lia.
  symmetry. apply (lpow_mul [S1] k 2).
Qed.

Lemma pow_01_append_0 (k : nat) (r : Stream sym) :
  [S0; S1] ^^ k *> ([S0] *> r) = [S0] *> ([S1; S0] ^^ k *> r).
Proof.
  exact (lpow_rotate [S1] S0 r k).
Qed.

Lemma shift_E_ones (k : nat) (l r : side) :
  l {{E}}> ([S1] ^^ k *> r) -->* (l <* [S1] ^^ k) {{E}}> r.
Proof.
  revert l r.
  induction k as [| k ih]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite lpow_succ_r_side.
  assert (h1 : l {{E}}> ([S1] *> ([S1] ^^ k *> r)) -->* (l <* [S1]) {{E}}> ([S1] ^^ k *> r))
    by fast_execute.
  pose proof (ih (l <* [S1]) r) as h2.
  rewrite lpow_one_l_side in h2.
  exact (etrans h1 h2).
Qed.

Lemma shift_CB_left (k : nat) (l r : side) :
  (l <* [S0; S1] ^^ k) {{C}}> ([S1] *> r) -->* l {{C}}> ([S1] *> ([S1; S1] ^^ k *> r)).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite lpow_split_l, lpow_1.
  assert (h1 : ((l <* [S0; S1] ^^ k) <* [S0; S1]) {{C}}> ([S1] *> r) -->*
               (l <* [S0; S1] ^^ k) {{C}}> ([S1] *> ([S1; S1] *> r)))
    by fast_execute.
  pose proof (ih l ([S1; S1] *> r)) as h2.
  rewrite lpow_one_r_side in h2.
  exact (etrans h1 h2).
Qed.

Lemma shift_D_right_100 (k : nat) (l r : side) :
  l {{D}}> ([S1; S0; S0] *> ([S1; S0] ^^ k *> r)) -->* (l <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> r).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite lpow_succ_r_side.
  assert (h1 : l {{D}}> ([S1; S0; S0] *> ([S1; S0] *> ([S1; S0] ^^ k *> r))) -->*
               (l <* [S0; S1]) {{D}}> ([S1; S0; S0] *> ([S1; S0] ^^ k *> r)))
    by fast_execute.
  pose proof (ih (l <* [S0; S1]) r) as h2.
  rewrite lpow_one_l_side in h2.
  exact (etrans h1 h2).
Qed.

Lemma shift_FA_left (k : nat) (l r : side) :
  (l <* [S1; S0] ^^ k) {{F}}> ([S0] *> r) -->* l {{F}}> ([S0] *> ([S0; S1] ^^ k *> r)).
Proof.
  revert l r.
  induction k as [| k ih]; intros l r; [apply evstep_refl |].
  replace (S k) with (k + 1) by lia.
  rewrite lpow_split_l, lpow_1.
  assert (h1 : ((l <* [S1; S0] ^^ k) <* [S1; S0]) {{F}}> ([S0] *> r) -->*
               (l <* [S1; S0] ^^ k) {{F}}> ([S0] *> ([S0; S1] *> r)))
    by fast_execute.
  pose proof (ih l ([S0; S1] *> r)) as h2.
  rewrite lpow_one_r_side in h2.
  exact (etrans h1 h2).
Qed.

Definition E_cfg (a b : nat) : Q * tape :=
  ((0inf <* [S1] ^^ b) <* [S1; S0] ^^ a) {{E}}> 0inf.

Definition F_R (b k : nat) (r : side) : Q * tape :=
  ((0inf <* [S1] ^^ b) <* [S1; S0] ^^ k) {{F}}> ([S0; S0] *> r).

Definition F_cfg (b k c : nat) : Q * tape :=
  ((0inf <* [S1] ^^ b) <* [S1; S0] ^^ k) {{F}}> ([S0; S0] *> ([S1] ^^ c *> 0inf)).

Lemma F_cfg_eq_F_R (b k c : nat) :
  F_cfg b k c = F_R b k ([S1] ^^ c *> 0inf).
Proof. reflexivity. Qed.

Lemma init_to_E : c0 -->+ E_cfg 0 4.
Proof.
  unfold c0, tape0, E_cfg; cbn [lpow Str_app app].
  fast_start_progress.
Qed.

Lemma step_E_b3_to_F (a b : nat) :
  E_cfg a (b + 3) -->+ F_cfg (b + 1) 0 (2 * a + 3).
Proof.
  unfold E_cfg, F_cfg.
  assert (h1 : ((0inf <* [S1] ^^ (b + 3)) <* [S1; S0] ^^ a) {{E}}> 0inf -->+
               (((0inf <* [S1] ^^ (b + 3)) <* [S1; S0] ^^ a) <* [S0]) {{C}}> ([S1] *> ([S1] *> 0inf)))
    by fast_start_progress.
  rewrite <- (append_zero_pow_01 (0inf <* [S1] ^^ (b + 3)) a) in h1.
  pose proof (shift_CB_left a ((0inf <* [S1] ^^ (b + 3)) <* [S0]) ([S1] *> 0inf)) as h2.
  rewrite pow_11_eq_pow_1_mul2 in h2.
  pose proof (ps_trans h1 h2) as h12.
  assert (h3 : ((((0inf <* [S1] ^^ b) <* [S1] ^^ 3) <* [S0]) {{C}}>
                 ([S1] *> ([S1] ^^ (2 * a) *> ([S1] *> 0inf)))) -->+
               (((0inf <* [S1] ^^ b) <* [S1] ^^ 1) <* [S1; S0] ^^ 0) {{F}}>
                 ([S0; S0] *> ([S1] ^^ 2 *> ([S1] ^^ (2 * a) *> ([S1] ^^ 1 *> 0inf))))).
  { cbn [lpow app Str_app]. fast_start_progress. }
  rewrite <- (lpow_split_l 0inf [S1] b 3), <- (lpow_split_l 0inf [S1] b 1) in h3.
  rewrite <- (lpow_split_r [S1] (2 * a) 1 0inf),
          <- (lpow_split_r [S1] 2 (2 * a + 1) 0inf) in h3.
  assert (ha : 2 + (2 * a + 1) = 2 * a + 3) by lia.
  rewrite ha in h3.
  exact (ptrans h12 h3).
Qed.

Lemma step_F_b2_k0 (c : nat) :
  F_cfg 2 0 (c + 1) -->+ F_cfg 5 0 c.
Proof.
  unfold F_cfg.
  rewrite (lpow_succ_r_side [S1] c 0inf).
  cbn [lpow app].
  fast_start_progress.
Qed.

Definition D100 (b k : nat) (r : side) : Q * tape :=
  (((0inf <* [S1] ^^ b) <* [S1; S0] ^^ k) <* [S0]) {{D}}> ([S1; S0; S0] *> r).

Definition C_bounce (b : nat) (s : side) : Q * tape :=
  ((0inf <* [S1] ^^ b) <* [S0]) {{C}}> ([S1] *> s).

Lemma step_F0_sweep_right (k : nat) (r : side) :
  0inf {{F}}> ([S0; S0] *> ([S1; S0] ^^ k *> r)) -->+
  (0inf <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> r).
Proof.
  assert (h1 : 0inf {{F}}> ([S0; S0] *> ([S1; S0] ^^ k *> r)) -->+
               0inf {{D}}> ([S1; S0; S0] *> ([S1; S0] ^^ k *> r)))
    by fast_start_progress.
  exact (ps_trans h1 (shift_D_right_100 k 0inf r)).
Qed.

Lemma F_R_b0_to_D100 (k : nat) (r : side) :
  F_R 0 k r -->+ D100 0 k r.
Proof.
  unfold F_R, D100; cbn [lpow Str_app].
  change (S0 >> S0 >> r) with ([S0] *> ([S0] *> r)).
  pose proof (shift_FA_left k 0inf ([S0] *> r)) as h1.
  rewrite pow_01_append_0 in h1.
  pose proof (step_F0_sweep_right k r) as h2.
  rewrite default_pow_01 in h2.
  change ([S0] *> ([S0] *> ([S1; S0] ^^ k *> r))) with ([S0; S0] *> ([S1; S0] ^^ k *> r)) in h1.
  exact (sp_trans h1 h2).
Qed.

Lemma F_R_b1_to_D100 (k : nat) (r : side) :
  F_R 1 k r -->+ D100 0 (k + 1) r.
Proof.
  unfold F_R, D100.
  change ([S0; S0] *> r) with ([S0] *> ([S0] *> r)).
  pose proof (shift_FA_left k (0inf <* [S1] ^^ 1) ([S0] *> r)) as h1.
  rewrite pow_01_append_0 in h1.
  assert (h2 : (0inf <* [S1] ^^ 1) {{F}}> ([S0] *> ([S0] *> ([S1; S0] ^^ k *> r))) -->+
               0inf {{F}}> ([S0; S0] *> ([S1; S0] *> ([S1; S0] ^^ k *> r)))).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_succ_r_side [S1; S0] k r) in h2.
  pose proof (step_F0_sweep_right (k + 1) r) as h3.
  rewrite default_pow_01 in h3.
  cbn [lpow Str_app] in *.
  exact (ptrans (sp_trans h1 h2) h3).
Qed.

Lemma F_R_b3_to_D100 (b k : nat) (r : side) :
  F_R (b + 3) k r -->+ D100 (b + 1) k r.
Proof.
  unfold F_R, D100.
  change ([S0; S0] *> r) with ([S0] *> ([S0] *> r)).
  pose proof (shift_FA_left k (0inf <* [S1] ^^ (b + 3)) ([S0] *> r)) as h1.
  rewrite pow_01_append_0 in h1.
  assert (h2 : ((0inf <* [S1] ^^ b) <* [S1] ^^ 3) {{F}}> ([S0] *> ([S0] *> ([S1; S0] ^^ k *> r))) -->+
               (((0inf <* [S1] ^^ b) <* [S1] ^^ 1) <* [S0]) {{D}}> ([S1; S0; S0] *> ([S1; S0] ^^ k *> r))).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l 0inf [S1] b 3), <- (lpow_split_l 0inf [S1] b 1) in h2.
  pose proof (shift_D_right_100 k ((0inf <* [S1] ^^ (b + 1)) <* [S0]) r) as h3.
  rewrite append_zero_pow_01 in h3.
  exact (ps_trans (sp_trans h1 h2) h3).
Qed.

Lemma D100_0_11 (k : nat) (r : side) :
  D100 0 k ([S1; S1] *> r) -->+ F_R 1 (k + 1) r.
Proof.
  unfold D100, F_R.
  change (0inf <* [S1] ^^ 0) with 0inf.
  rewrite <- default_pow_01.
  assert (h1 : (0inf <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> ([S1; S1] *> r)) -->+
               (((0inf <* [S0; S1] ^^ k) <* [S0; S1] ^^ 1) <* [S1]) {{F}}> ([S0; S0] *> r)).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l 0inf [S0; S1] k 1),
          <- append_one_pow_10 in h1.
  change (0inf <* [S1]) with (0inf <* [S1] ^^ 1) in h1.
  exact h1.
Qed.

Lemma D100_succ_11 (b k : nat) (r : side) :
  D100 (b + 1) k ([S1; S1] *> r) -->+ F_R (b + 1) (k + 2) r.
Proof.
  unfold D100, F_R.
  assert (h1 : (((0inf <* [S1] ^^ (b + 1)) <* [S1; S0] ^^ k) <* [S0]) {{D}}> ([S1; S0; S0] *> ([S1; S1] *> r)) -->+
               (((0inf <* [S1] ^^ (b + 1)) <* [S1; S0] ^^ k) <* [S1; S0] ^^ 2) {{F}}> ([S0; S0] *> r)).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l (0inf <* [S1] ^^ (b + 1)) [S1; S0] k 2) in h1.
  exact h1.
Qed.

Lemma D100_nil_to_C_bounce (b k : nat) :
  D100 b k 0inf -->+ C_bounce b ([S1] ^^ (2 * k + 3) *> 0inf).
Proof.
  unfold D100, C_bounce.
  rewrite <- append_zero_pow_01.
  assert (h1 : (((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> 0inf) -->+
               ((((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) <* [S0; S1] ^^ 1) {{C}}> ([S1] *> ([S1] ^^ 1 *> 0inf))).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l ((0inf <* [S1] ^^ b) <* [S0]) [S0; S1] k 1) in h1.
  pose proof (shift_CB_left (k + 1) ((0inf <* [S1] ^^ b) <* [S0]) ([S1] ^^ 1 *> 0inf)) as h2.
  rewrite pow_11_eq_pow_1_mul2, <- (lpow_split_r [S1] (2 * (k + 1)) 1 0inf) in h2.
  replace (2 * (k + 1) + 1) with (2 * k + 3) in h2 by lia.
  exact (ps_trans h1 h2).
Qed.

Lemma D100_one_to_C_bounce (b k : nat) :
  D100 b k ([S1] *> 0inf) -->+ C_bounce b ([S1] ^^ (2 * k + 5) *> 0inf).
Proof.
  unfold D100, C_bounce.
  rewrite <- append_zero_pow_01.
  assert (h1 : (((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> ([S1] *> 0inf)) -->+
               ((((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) <* [S0; S1] ^^ 2) {{C}}> ([S1] *> ([S1] ^^ 1 *> 0inf))).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l ((0inf <* [S1] ^^ b) <* [S0]) [S0; S1] k 2) in h1.
  pose proof (shift_CB_left (k + 2) ((0inf <* [S1] ^^ b) <* [S0]) ([S1] ^^ 1 *> 0inf)) as h2.
  rewrite pow_11_eq_pow_1_mul2, <- (lpow_split_r [S1] (2 * (k + 2)) 1 0inf) in h2.
  replace (2 * (k + 2) + 1) with (2 * k + 5) in h2 by lia.
  exact (ps_trans h1 h2).
Qed.

Lemma D100_01_to_C_bounce (b k : nat) (r : side) :
  D100 b k ([S0; S1] *> r) -->+ C_bounce b ([S1] ^^ (2 * k + 4) *> r).
Proof.
  unfold D100, C_bounce.
  rewrite <- append_zero_pow_01.
  assert (h1 : (((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) {{D}}> ([S1; S0; S0] *> ([S0; S1] *> r)) -->+
               ((((0inf <* [S1] ^^ b) <* [S0]) <* [S0; S1] ^^ k) <* [S0; S1] ^^ 1) {{C}}> ([S1] *> ([S1] ^^ 2 *> r))).
  { cbn [lpow app]. fast_start_progress. }
  rewrite <- (lpow_split_l ((0inf <* [S1] ^^ b) <* [S0]) [S0; S1] k 1) in h1.
  pose proof (shift_CB_left (k + 1) ((0inf <* [S1] ^^ b) <* [S0]) ([S1] ^^ 2 *> r)) as h2.
  rewrite pow_11_eq_pow_1_mul2, <- (lpow_split_r [S1] (2 * (k + 1)) 2 r) in h2.
  replace (2 * (k + 1) + 2) with (2 * k + 4) in h2 by lia.
  exact (ps_trans h1 h2).
Qed.

Lemma C_bounce_0 (s : side) :
  C_bounce 0 s -->+ (0inf <* [S1] ^^ 3) {{E}}> s.
Proof.
  unfold C_bounce; cbn [lpow app]. fast_start_progress.
Qed.

Lemma C_bounce_1 (s : side) :
  C_bounce 1 s -->+ (0inf <* [S1] ^^ 5) {{E}}> s.
Proof.
  unfold C_bounce; cbn [lpow app]. fast_start_progress.
Qed.

Lemma C_bounce_3 (b : nat) (s : side) :
  C_bounce (b + 3) s -->+ F_R (b + 1) 0 ([S1] ^^ 2 *> s).
Proof.
  unfold C_bounce, F_R.
  rewrite (lpow_split_l 0inf [S1] b 3), (lpow_split_l 0inf [S1] b 1).
  cbn [lpow app]. fast_start_progress.
Qed.

Lemma step_F_ksucc_c0 (b k : nat) :
  F_cfg b (k + 1) 0 -->+ F_cfg b k 1.
Proof.
  unfold F_cfg.
  rewrite (lpow_split_l (0inf <* [S1] ^^ b) [S1; S0] k 1).
  cbn [lpow app]. fast_start_progress.
Qed.

Lemma step_F_b2_k0_c0 :
  F_cfg 2 0 0 -->+ F_cfg 3 0 3.
Proof.
  unfold F_cfg; cbn [lpow app]. fast_start_progress.
Qed.

Lemma step_F_R_b2_one (k : nat) (r : side) :
  F_R 2 k ([S1] *> r) -->+ F_R 5 0 ([S0; S1] ^^ k *> r).
Proof.
  unfold F_R.
  change ([S0; S0] *> ([S1] *> r)) with ([S0] *> ([S0; S1] *> r)).
  pose proof (shift_FA_left k (0inf <* [S1] ^^ 2) ([S0; S1] *> r)) as h1.
  assert (h2 : (0inf <* [S1] ^^ 2) {{F}}> ([S0] *> ([S0; S1] ^^ k *> ([S0; S1] *> r))) -->+
               ((0inf <* [S1] ^^ 5) <* [S1; S0] ^^ 0) {{F}}> ([S0; S0] *> ([S0; S1] ^^ k *> r))).
  { rewrite (lpow_one_r_side [S0; S1] k r), (lpow_succ_r_side [S0; S1] k r).
    cbn [lpow app]. fast_start_progress. }
  exact (sp_trans h1 h2).
Qed.

Lemma step_E_01_to_F_R (b : nat) (r : side) :
  (0inf <* [S1] ^^ b) {{E}}> ([S0; S1] *> r) -->+ F_R b 0 r.
Proof.
  unfold F_R; cbn [lpow app]. fast_start_progress.
Qed.

Lemma C_bounce_0_ones (n : nat) :
  C_bounce 0 ([S1] ^^ n *> 0inf) -->+ F_cfg (n + 1) 0 3.
Proof.
  pose proof (C_bounce_0 ([S1] ^^ n *> 0inf)) as h1.
  pose proof (shift_E_ones n (0inf <* [S1] ^^ 3) 0inf) as h2.
  rewrite <- (lpow_split_l 0inf [S1] 3 n) in h2.
  replace (3 + n) with (n + 3) in h2 by lia.
  change ((0inf <* [S1] ^^ (n + 3)) {{E}}> 0inf) with (E_cfg 0 (n + 3)) in h2.
  pose proof (step_E_b3_to_F 0 n) as h3.
  cbn [Nat.mul Nat.add] in h3.
  exact (ptrans (ps_trans h1 h2) h3).
Qed.

Lemma C_bounce_1_ones (n : nat) :
  C_bounce 1 ([S1] ^^ n *> 0inf) -->+ F_cfg (n + 3) 0 3.
Proof.
  pose proof (C_bounce_1 ([S1] ^^ n *> 0inf)) as h1.
  pose proof (shift_E_ones n (0inf <* [S1] ^^ 5) 0inf) as h2.
  rewrite <- (lpow_split_l 0inf [S1] 5 n) in h2.
  replace (5 + n) with ((n + 2) + 3) in h2 by lia.
  change ((0inf <* [S1] ^^ ((n + 2) + 3)) {{E}}> 0inf) with (E_cfg 0 ((n + 2) + 3)) in h2.
  pose proof (step_E_b3_to_F 0 (n + 2)) as h3.
  replace ((n + 2) + 1) with (n + 3) in h3 by lia.
  cbn [Nat.mul Nat.add] in h3.
  exact (ptrans (ps_trans h1 h2) h3).
Qed.

Lemma C_bounce_3_ones (b n : nat) :
  C_bounce (b + 3) ([S1] ^^ n *> 0inf) -->+ F_cfg (b + 1) 0 (n + 2).
Proof.
  pose proof (C_bounce_3 b ([S1] ^^ n *> 0inf)) as h1.
  rewrite <- (lpow_split_r [S1] 2 n 0inf), <- F_cfg_eq_F_R in h1.
  replace (2 + n) with (n + 2) in h1 by lia.
  exact h1.
Qed.

Lemma rule_F_ksucc_c0 (b k : nat) :
  F_cfg b (k + 1) 0 -->+ F_cfg b k 1.
Proof. exact (step_F_ksucc_c0 b k). Qed.

Lemma rule_F_b0_k0_c0 :
  F_cfg 0 0 0 -->+ F_cfg 4 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b0_to_D100 0 0inf) (D100_nil_to_C_bounce 0 0)) (C_bounce_0_ones 3)).
Qed.

Lemma rule_F_b1_k0_c0 :
  F_cfg 1 0 0 -->+ F_cfg 6 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b1_to_D100 0 0inf) (D100_nil_to_C_bounce 0 1)) (C_bounce_0_ones 5)).
Qed.

Lemma rule_F_b2_k0_c0 :
  F_cfg 2 0 0 -->+ F_cfg 3 0 3.
Proof. exact step_F_b2_k0_c0. Qed.

Lemma rule_F_b3_k0_c0 :
  F_cfg 3 0 0 -->+ F_cfg 6 0 3.
Proof.
  exact (ptrans (ptrans (F_R_b3_to_D100 0 0 0inf) (D100_nil_to_C_bounce 1 0)) (C_bounce_1_ones 3)).
Qed.

Lemma rule_F_b5_k0_c0 (b : nat) :
  F_cfg (b + 5) 0 0 -->+ F_cfg (b + 1) 0 5.
Proof.
  replace (b + 5) with ((b + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (b + 2) 0 0inf) as h1.
  replace ((b + 2) + 1) with (b + 3) in h1 by lia.
  exact (ptrans (ptrans h1 (D100_nil_to_C_bounce (b + 3) 0))
                (C_bounce_3_ones b 3)).
Qed.

Lemma rule_F_b0_c1 (k : nat) :
  F_cfg 0 k 1 -->+ F_cfg (2 * k + 6) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b0_to_D100 k ([S1] *> 0inf)) (D100_one_to_C_bounce 0 k))
                     (C_bounce_0_ones (2 * k + 5))) as h.
  replace ((2 * k + 5) + 1) with (2 * k + 6) in h by lia.
  exact h.
Qed.

Lemma rule_F_b1_c1 (k : nat) :
  F_cfg 1 k 1 -->+ F_cfg (2 * k + 8) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b1_to_D100 k ([S1] *> 0inf)) (D100_one_to_C_bounce 0 (k + 1)))
                     (C_bounce_0_ones (2 * (k + 1) + 5))) as h.
  replace ((2 * (k + 1) + 5) + 1) with (2 * k + 8) in h by lia.
  exact h.
Qed.

Lemma rule_F_b2_k0_c1 (c : nat) :
  F_cfg 2 0 (c + 1) -->+ F_cfg 5 0 c.
Proof. exact (step_F_b2_k0 c). Qed.

Lemma rule_F_b3_c1 (k : nat) :
  F_cfg 3 k 1 -->+ F_cfg (2 * k + 8) 0 3.
Proof.
  pose proof (ptrans (ptrans (F_R_b3_to_D100 0 k ([S1] *> 0inf)) (D100_one_to_C_bounce 1 k))
                     (C_bounce_1_ones (2 * k + 5))) as h.
  replace ((2 * k + 5) + 3) with (2 * k + 8) in h by lia.
  exact h.
Qed.

Lemma rule_F_b5_c1 (b k : nat) :
  F_cfg (b + 5) k 1 -->+ F_cfg (b + 1) 0 (2 * k + 7).
Proof.
  replace (b + 5) with ((b + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (b + 2) k ([S1] *> 0inf)) as h1.
  replace ((b + 2) + 1) with (b + 3) in h1 by lia.
  pose proof (ptrans (ptrans h1 (D100_one_to_C_bounce (b + 3) k))
                     (C_bounce_3_ones b (2 * k + 5))) as h.
  replace ((2 * k + 5) + 2) with (2 * k + 7) in h by lia.
  exact h.
Qed.

Lemma rule_F_b0_c2 (k c : nat) :
  F_cfg 0 k (c + 2) -->+ F_cfg 1 (k + 1) c.
Proof.
  assert (hc : [S1] ^^ (c + 2) *> 0inf = [S1; S1] *> ([S1] ^^ c *> 0inf)).
  { replace (c + 2) with (2 + c) by lia. rewrite lpow_split_r. reflexivity. }
  rewrite F_cfg_eq_F_R, hc.
  exact (ptrans (F_R_b0_to_D100 k ([S1; S1] *> ([S1] ^^ c *> 0inf)))
                (D100_0_11 k ([S1] ^^ c *> 0inf))).
Qed.

Lemma rule_F_b1_c2 (k c : nat) :
  F_cfg 1 k (c + 2) -->+ F_cfg 1 (k + 2) c.
Proof.
  assert (hc : [S1] ^^ (c + 2) *> 0inf = [S1; S1] *> ([S1] ^^ c *> 0inf)).
  { replace (c + 2) with (2 + c) by lia. rewrite lpow_split_r. reflexivity. }
  rewrite F_cfg_eq_F_R, hc.
  pose proof (D100_0_11 (k + 1) ([S1] ^^ c *> 0inf)) as h2.
  replace ((k + 1) + 1) with (k + 2) in h2 by lia.
  exact (ptrans (F_R_b1_to_D100 k ([S1; S1] *> ([S1] ^^ c *> 0inf))) h2).
Qed.

Lemma rule_F_b3_c2 (b k c : nat) :
  F_cfg (b + 3) k (c + 2) -->+ F_cfg (b + 1) (k + 2) c.
Proof.
  assert (hc : [S1] ^^ (c + 2) *> 0inf = [S1; S1] *> ([S1] ^^ c *> 0inf)).
  { replace (c + 2) with (2 + c) by lia. rewrite lpow_split_r. reflexivity. }
  rewrite F_cfg_eq_F_R, hc.
  exact (ptrans (F_R_b3_to_D100 b k ([S1; S1] *> ([S1] ^^ c *> 0inf)))
                (D100_succ_11 b k ([S1] ^^ c *> 0inf))).
Qed.

Definition Odd_cfg (p k n m c : nat) : Q * tape :=
  F_R (2 * p + 1) k ([S1] ^^ (2 * n) *> ([S0; S1] ^^ (m + 1) *> ([S1] ^^ c *> 0inf))).

Definition ETail_cfg (k m c : nat) : Q * tape :=
  (0inf <* [S1] ^^ (2 * (k + 4) + 1)) {{E}}> ([S0; S1] ^^ m *> ([S1] ^^ c *> 0inf)).

Lemma rule_F_b2_ksucc_c1 (k c : nat) :
  F_cfg 2 (k + 1) (c + 1) -->+ Odd_cfg 2 0 0 k c.
Proof.
  unfold Odd_cfg; cbn [Nat.mul lpow Str_app].
  rewrite F_cfg_eq_F_R, (lpow_succ_r_side [S1] c 0inf).
  exact (step_F_R_b2_one (k + 1) ([S1] ^^ c *> 0inf)).
Qed.

Lemma step_Odd_nsucc_p0 (k n m c : nat) :
  Odd_cfg 0 k (n + 1) m c -->+ Odd_cfg 0 (k + 2) n m c.
Proof.
  unfold Odd_cfg.
  set (r := [S0; S1] ^^ (m + 1) *> ([S1] ^^ c *> 0inf)).
  replace (2 * (n + 1)) with (2 + 2 * n) by lia.
  rewrite (lpow_split_r [S1] 2 (2 * n) r).
  cbn [Nat.mul Nat.add].
  pose proof (D100_0_11 (k + 1) ([S1] ^^ (n + (n + 0)) *> r)) as h2.
  replace ((k + 1) + 1) with (k + 2) in h2 by lia.
  exact (ptrans (F_R_b1_to_D100 k ([S1] ^^ 2 *> ([S1] ^^ (n + (n + 0)) *> r))) h2).
Qed.

Lemma step_Odd_nsucc_psucc (p k n m c : nat) :
  Odd_cfg (p + 1) k (n + 1) m c -->+ Odd_cfg p (k + 2) n m c.
Proof.
  unfold Odd_cfg.
  set (r := [S0; S1] ^^ (m + 1) *> ([S1] ^^ c *> 0inf)).
  replace (2 * (n + 1)) with (2 + 2 * n) by lia.
  replace (2 * (p + 1) + 1) with (2 * p + 3) by lia.
  rewrite (lpow_split_r [S1] 2 (2 * n) r).
  pose proof (ptrans (F_R_b3_to_D100 (2 * p) k ([S1] ^^ 2 *> ([S1] ^^ (2 * n) *> r)))
                     (D100_succ_11 (2 * p) k ([S1] ^^ (2 * n) *> r))) as h.
  exact h.
Qed.

Lemma step_Odd_n0_p0 (k m c : nat) :
  Odd_cfg 0 k 0 m c -->+ ETail_cfg k m c.
Proof.
  unfold Odd_cfg, ETail_cfg; cbn [Nat.mul Nat.add lpow Str_app].
  rewrite (lpow_succ_r_side [S0; S1] m ([S1] ^^ c *> 0inf)).
  set (r' := [S0; S1] ^^ m *> ([S1] ^^ c *> 0inf)).
  pose proof (F_R_b1_to_D100 k ([S0; S1] *> r')) as h1.
  pose proof (D100_01_to_C_bounce 0 (k + 1) r') as h2.
  pose proof (C_bounce_0 ([S1] ^^ (2 * (k + 1) + 4) *> r')) as h3.
  pose proof (shift_E_ones (2 * (k + 1) + 4) (0inf <* [S1] ^^ 3) r') as h4.
  rewrite <- (lpow_split_l 0inf [S1] 3 (2 * (k + 1) + 4)) in h4.
  replace (3 + (2 * (k + 1) + 4)) with (2 * (k + 4) + 1) in h4 by lia.
  exact (ps_trans (ptrans (ptrans h1 h2) h3) h4).
Qed.

Lemma step_Odd_n0_p1 (k m c : nat) :
  Odd_cfg 1 k 0 m c -->+ ETail_cfg k m c.
Proof.
  unfold Odd_cfg, ETail_cfg; cbn [Nat.mul lpow Str_app].
  rewrite (lpow_succ_r_side [S0; S1] m ([S1] ^^ c *> 0inf)).
  set (r' := [S0; S1] ^^ m *> ([S1] ^^ c *> 0inf)).
  change (2 + 1) with (0 + 3).
  pose proof (F_R_b3_to_D100 0 k ([S0; S1] *> r')) as h1.
  pose proof (D100_01_to_C_bounce 1 k r') as h2.
  pose proof (C_bounce_1 ([S1] ^^ (2 * k + 4) *> r')) as h3.
  pose proof (shift_E_ones (2 * k + 4) (0inf <* [S1] ^^ 5) r') as h4.
  rewrite <- (lpow_split_l 0inf [S1] 5 (2 * k + 4)) in h4.
  replace (5 + (2 * k + 4)) with (2 * (k + 4) + 1) in h4 by lia.
  exact (ps_trans (ptrans (ptrans h1 h2) h3) h4).
Qed.

Lemma step_Odd_n0_p2_m0 (p k c : nat) :
  Odd_cfg (p + 2) k 0 0 c -->+ F_cfg (2 * p + 1) 0 (2 * (k + 3) + c).
Proof.
  unfold Odd_cfg.
  set (r' := [S1] ^^ c *> 0inf).
  change ([S1] ^^ (2 * 0) *> ([S0; S1] ^^ (0 + 1) *> r')) with ([S0; S1] *> r').
  replace (2 * (p + 2) + 1) with ((2 * p + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (2 * p + 2) k ([S0; S1] *> r')) as h1.
  replace ((2 * p + 2) + 1) with (2 * p + 3) in h1 by lia.
  pose proof (D100_01_to_C_bounce (2 * p + 3) k r') as h2.
  pose proof (C_bounce_3 (2 * p) ([S1] ^^ (2 * k + 4) *> r')) as h3.
  rewrite <- (lpow_split_r [S1] 2 (2 * k + 4) r') in h3.
  replace (2 + (2 * k + 4)) with (2 * (k + 3)) in h3 by lia.
  unfold r' in h3.
  rewrite <- (lpow_split_r [S1] (2 * (k + 3)) c 0inf), <- F_cfg_eq_F_R in h3.
  exact (ptrans (ptrans h1 h2) h3).
Qed.

Lemma step_Odd_n0_p2_msucc (p k m c : nat) :
  Odd_cfg (p + 2) k 0 (m + 1) c -->+ Odd_cfg p 0 (k + 3) m c.
Proof.
  unfold Odd_cfg.
  change (2 * 0) with 0; cbn [lpow Str_app].
  rewrite (lpow_succ_r_side [S0; S1] (m + 1) ([S1] ^^ c *> 0inf)).
  set (r' := [S0; S1] ^^ (m + 1) *> ([S1] ^^ c *> 0inf)).
  replace (2 * (p + 2) + 1) with ((2 * p + 2) + 3) by lia.
  pose proof (F_R_b3_to_D100 (2 * p + 2) k ([S0; S1] *> r')) as h1.
  replace ((2 * p + 2) + 1) with (2 * p + 3) in h1 by lia.
  pose proof (D100_01_to_C_bounce (2 * p + 3) k r') as h2.
  pose proof (C_bounce_3 (2 * p) ([S1] ^^ (2 * k + 4) *> r')) as h3.
  rewrite <- (lpow_split_r [S1] 2 (2 * k + 4) r') in h3.
  replace (2 + (2 * k + 4)) with (2 * (k + 3)) in h3 by lia.
  exact (ptrans (ptrans h1 h2) h3).
Qed.

Lemma step_ETail_m0 (k c : nat) :
  ETail_cfg k 0 c -->+ F_cfg (2 * k + c + 7) 0 3.
Proof.
  unfold ETail_cfg; cbn [lpow Str_app].
  pose proof (shift_E_ones c (0inf <* [S1] ^^ (2 * (k + 4) + 1)) 0inf) as h1.
  rewrite <- (lpow_split_l 0inf [S1] (2 * (k + 4) + 1) c) in h1.
  replace (2 * (k + 4) + 1 + c) with ((2 * k + c + 6) + 3) in h1 by lia.
  change ((0inf <* [S1] ^^ ((2 * k + c + 6) + 3)) {{E}}> 0inf)
    with (E_cfg 0 ((2 * k + c + 6) + 3)) in h1.
  pose proof (step_E_b3_to_F 0 (2 * k + c + 6)) as h2.
  replace ((2 * k + c + 6) + 1) with (2 * k + c + 7) in h2 by lia.
  cbn [Nat.mul Nat.add] in h2.
  exact (sp_trans h1 h2).
Qed.

Lemma step_ETail_m1 (k c : nat) :
  ETail_cfg k 1 c -->+ F_cfg (2 * (k + 4) + 1) 0 c.
Proof.
  unfold ETail_cfg.
  rewrite lpow_1, F_cfg_eq_F_R.
  exact (step_E_01_to_F_R (2 * (k + 4) + 1) ([S1] ^^ c *> 0inf)).
Qed.

Lemma step_ETail_m2 (k m c : nat) :
  ETail_cfg k (m + 2) c -->+ Odd_cfg (k + 4) 0 0 m c.
Proof.
  unfold ETail_cfg, Odd_cfg.
  change (2 * 0) with 0; cbn [lpow Str_app].
  replace (m + 2) with ((m + 1) + 1) by lia.
  rewrite (lpow_succ_r_side [S0; S1] (m + 1) ([S1] ^^ c *> 0inf)).
  exact (step_E_01_to_F_R (2 * (k + 4) + 1) ([S0; S1] ^^ (m + 1) *> ([S1] ^^ c *> 0inf))).
Qed.


(* ========================================================================== *)
(* Layer 2: Symbolic Acceleration State Space & Exponential Macro-Rules       *)
(* ========================================================================== *)

Close Scope nat_scope.
Open Scope N_scope.

Lemma N_peano_ind (P : N -> Prop) :
  P 0 -> (forall n, P n -> P (n + 1)) -> forall n, P n.
Proof.
  intros H0 Hstep n.
  induction n using N.peano_ind.
  - exact H0.
  - replace (N.succ n) with (n + 1) by lia.
    exact (Hstep n IHn).
Qed.

Lemma pow2_add (a b : N) : 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. exact (N.pow_add_r 2 a b). Qed.

Lemma pow2_succ (n : N) : 2 ^ (n + 1) = 2 ^ n * 2.
Proof. rewrite pow2_add. change (2 ^ 1) with 2. reflexivity. Qed.

Inductive State : Type :=
  | stA (b k c : N)
  | stOdd (p k n m c : N)
  | stETail (k m c : N).

Definition start : State := stA 5 0 2.

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

Definition encode (s : State) : Q * tape :=
  match s with
  | stA b k c => F_cfg (N.to_nat b) (N.to_nat k) (N.to_nat c)
  | stOdd p k n m c => Odd_cfg (N.to_nat p) (N.to_nat k) (N.to_nat n) (N.to_nat m) (N.to_nat c)
  | stETail k m c => ETail_cfg (N.to_nat k) (N.to_nat m) (N.to_nat c)
  end.

Lemma init_reaches_start : c0 -->+ encode start.
Proof.
  exact (ptrans init_to_E (ptrans (step_E_b3_to_F 0 1) (step_F_b2_k0 2))).
Qed.

Ltac rew_neq a b :=
  let H := fresh in
  assert (H : (a =? b) = false) by (apply N.eqb_neq; lia);
  rewrite H; clear H; cbn [N.eqb Pos.eqb].

Ltac rew_eq a b :=
  let H := fresh in
  assert (H : (a =? b) = true) by (apply N.eqb_eq; lia);
  rewrite H; clear H; cbn [N.eqb Pos.eqb].

Lemma eq_some_inj {A : Type} {x y : A} : Some x = Some y -> x = y.
Proof. congruence. Qed.

Ltac split_eqb_in H :=
  cbn iota in H;
  match type of H with
  | context [if ?x =? ?y then _ else _] =>
    let Heq := fresh "Heq" in
    destruct (x =? y) eqn:Heq;
    cbn iota in H;
    [apply N.eqb_eq in Heq; try subst x | apply N.eqb_neq in Heq]
  end.

Lemma step_sound {s s' : State} (hnext : next s = Some s') :
  encode s -->+ encode s'.
Proof.
  destruct s as [b k c | p k n m c | k m c];
  unfold next in hnext;
  repeat split_eqb_in hnext;
  try discriminate;
  apply eq_some_inj in hnext; subst.
  - exact rule_F_b0_k0_c0.
  - exact rule_F_b1_k0_c0.
  - exact rule_F_b2_k0_c0.
  - exact rule_F_b3_k0_c0.
  - unfold encode.
    replace (N.to_nat b) with (N.to_nat (b - 5) + 5)%nat by lia.
    replace (N.to_nat (b - 4)) with (N.to_nat (b - 5) + 1)%nat by lia.
    exact (rule_F_b5_k0_c0 (N.to_nat (b - 5))).
  - unfold encode.
    replace (N.to_nat k) with (N.to_nat (k - 1) + 1)%nat by lia.
    exact (rule_F_ksucc_c0 (N.to_nat b) (N.to_nat (k - 1))).
  - unfold encode.
    replace (N.to_nat (2 * k + 6)) with (2 * N.to_nat k + 6)%nat by lia.
    exact (rule_F_b0_c1 (N.to_nat k)).
  - unfold encode.
    replace (N.to_nat (2 * k + 8)) with (2 * N.to_nat k + 8)%nat by lia.
    exact (rule_F_b1_c1 (N.to_nat k)).
  - exact (rule_F_b2_k0_c1 0).
  - unfold encode.
    replace (N.to_nat k) with (N.to_nat (k - 1) + 1)%nat by lia.
    exact (rule_F_b2_ksucc_c1 (N.to_nat (k - 1)) 0).
  - unfold encode.
    replace (N.to_nat (2 * k + 8)) with (2 * N.to_nat k + 8)%nat by lia.
    exact (rule_F_b3_c1 (N.to_nat k)).
  - unfold encode.
    replace (N.to_nat b) with (N.to_nat (b - 5) + 5)%nat by lia.
    replace (N.to_nat (b - 4)) with (N.to_nat (b - 5) + 1)%nat by lia.
    replace (N.to_nat (2 * k + 7)) with (2 * N.to_nat k + 7)%nat by lia.
    exact (rule_F_b5_c1 (N.to_nat (b - 5)) (N.to_nat k)).
  - unfold encode.
    replace (N.to_nat c) with (N.to_nat (c - 2) + 2)%nat by lia.
    replace (N.to_nat (k + 1)) with (N.to_nat k + 1)%nat by lia.
    exact (rule_F_b0_c2 (N.to_nat k) (N.to_nat (c - 2))).
  - unfold encode.
    replace (N.to_nat c) with (N.to_nat (c - 2) + 2)%nat by lia.
    replace (N.to_nat (k + 2)) with (N.to_nat k + 2)%nat by lia.
    exact (rule_F_b1_c2 (N.to_nat k) (N.to_nat (c - 2))).
  - unfold encode.
    replace (N.to_nat c) with (N.to_nat (c - 1) + 1)%nat by lia.
    exact (rule_F_b2_k0_c1 (N.to_nat (c - 1))).
  - unfold encode.
    replace (N.to_nat k) with (N.to_nat (k - 1) + 1)%nat by lia.
    replace (N.to_nat c) with (N.to_nat (c - 1) + 1)%nat by lia.
    exact (rule_F_b2_ksucc_c1 (N.to_nat (k - 1)) (N.to_nat (c - 1))).
  - unfold encode.
    replace (N.to_nat b) with (N.to_nat (b - 3) + 3)%nat by lia.
    replace (N.to_nat (b - 2)) with (N.to_nat (b - 3) + 1)%nat by lia.
    replace (N.to_nat (k + 2)) with (N.to_nat k + 2)%nat by lia.
    replace (N.to_nat c) with (N.to_nat (c - 2) + 2)%nat by lia.
    exact (rule_F_b3_c2 (N.to_nat (b - 3)) (N.to_nat k) (N.to_nat (c - 2))).
  - exact (step_Odd_n0_p0 (N.to_nat k) (N.to_nat m) (N.to_nat c)).
  - exact (step_Odd_n0_p1 (N.to_nat k) (N.to_nat m) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat p) with (N.to_nat (p - 2) + 2)%nat by lia.
    replace (N.to_nat (2 * (p - 2) + 1)) with (2 * N.to_nat (p - 2) + 1)%nat by lia.
    replace (N.to_nat (2 * (k + 3) + c)) with (2 * (N.to_nat k + 3) + N.to_nat c)%nat by lia.
    exact (step_Odd_n0_p2_m0 (N.to_nat (p - 2)) (N.to_nat k) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat p) with (N.to_nat (p - 2) + 2)%nat by lia.
    replace (N.to_nat m) with (N.to_nat (m - 1) + 1)%nat by lia.
    replace (N.to_nat (k + 3)) with (N.to_nat k + 3)%nat by lia.
    exact (step_Odd_n0_p2_msucc (N.to_nat (p - 2)) (N.to_nat k) (N.to_nat (m - 1)) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat n) with (N.to_nat (n - 1) + 1)%nat by lia.
    replace (N.to_nat (k + 2)) with (N.to_nat k + 2)%nat by lia.
    exact (step_Odd_nsucc_p0 (N.to_nat k) (N.to_nat (n - 1)) (N.to_nat m) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat p) with (N.to_nat (p - 1) + 1)%nat by lia.
    replace (N.to_nat n) with (N.to_nat (n - 1) + 1)%nat by lia.
    replace (N.to_nat (k + 2)) with (N.to_nat k + 2)%nat by lia.
    exact (step_Odd_nsucc_psucc (N.to_nat (p - 1)) (N.to_nat k) (N.to_nat (n - 1)) (N.to_nat m) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat (2 * k + c + 7)) with (2 * N.to_nat k + N.to_nat c + 7)%nat by lia.
    exact (step_ETail_m0 (N.to_nat k) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat (2 * (k + 4) + 1)) with (2 * (N.to_nat k + 4) + 1)%nat by lia.
    exact (step_ETail_m1 (N.to_nat k) (N.to_nat c)).
  - unfold encode.
    replace (N.to_nat m) with (N.to_nat (m - 2) + 2)%nat by lia.
    replace (N.to_nat (k + 4)) with (N.to_nat k + 4)%nat by lia.
    exact (step_ETail_m2 (N.to_nat k) (N.to_nat (m - 2)) (N.to_nat c)).
Qed.

Inductive OrbitReachesStar (f : State -> option State) : State -> State -> Prop :=
  | ors_refl s : OrbitReachesStar f s s
  | ors_step s1 s2 s3 : f s1 = Some s2 -> OrbitReachesStar f s2 s3 -> OrbitReachesStar f s1 s3.

Inductive OrbitReachesPlus (f : State -> option State) : State -> State -> Prop :=
  | orp_step s1 s2 s3 : f s1 = Some s2 -> OrbitReachesStar f s2 s3 -> OrbitReachesPlus f s1 s3.

Lemma ors_single {f : State -> option State} {s1 s2 : State} (h : f s1 = Some s2) :
  OrbitReachesStar f s1 s2.
Proof. exact (ors_step f s1 s2 s2 h (ors_refl f s2)). Qed.

Lemma ors_trans {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitReachesStar f s1 s2) (h2 : OrbitReachesStar f s2 s3) :
  OrbitReachesStar f s1 s3.
Proof.
  induction h1 as [s | a b c hab _ ih]; [exact h2 |].
  exact (ors_step f a b s3 hab (ih h2)).
Qed.

Lemma orp_single {f : State -> option State} {s1 s2 : State} (h : f s1 = Some s2) :
  OrbitReachesPlus f s1 s2.
Proof. exact (orp_step f s1 s2 s2 h (ors_refl f s2)). Qed.

Lemma orp_step2 {f : State -> option State} {s1 s2 s3 : State}
    (h1 : f s1 = Some s2) (h2 : f s2 = Some s3) :
  OrbitReachesPlus f s1 s3.
Proof. exact (orp_step f s1 s2 s3 h1 (ors_single h2)). Qed.

Lemma orp_to_star {f : State -> option State} {s1 s2 : State}
    (h : OrbitReachesPlus f s1 s2) :
  OrbitReachesStar f s1 s2.
Proof. destruct h as [a b c hab hbc]; exact (ors_step f a b c hab hbc). Qed.

Lemma orp_trans_star {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitReachesPlus f s1 s2) (h2 : OrbitReachesStar f s2 s3) :
  OrbitReachesPlus f s1 s3.
Proof. destruct h1 as [a b c hab hbc]; exact (orp_step f a b s3 hab (ors_trans hbc h2)). Qed.

Lemma ors_trans_plus {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitReachesStar f s1 s2) (h2 : OrbitReachesPlus f s2 s3) :
  OrbitReachesPlus f s1 s3.
Proof.
  induction h1 as [s | a b c hab _ ih]; [exact h2 |].
  exact (orp_step f a b s3 hab (orp_to_star (ih h2))).
Qed.

Lemma orp_trans {f : State -> option State} {s1 s2 s3 : State}
    (h1 : OrbitReachesPlus f s1 s2) (h2 : OrbitReachesPlus f s2 s3) :
  OrbitReachesPlus f s1 s3.
Proof. exact (orp_trans_star h1 (orp_to_star h2)). Qed.

Fixpoint iterOpt (f : State -> option State) (n : nat) (s : State) : option State :=
  match n with
  | O => Some s
  | S m =>
    match f s with
    | Some s' => iterOpt f m s'
    | None => None
    end
  end.

Lemma iterOpt_reaches_star (f : State -> option State) (n : nat) (s1 s2 : State) :
  iterOpt f n s1 = Some s2 -> OrbitReachesStar f s1 s2.
Proof.
  revert s1.
  induction n as [| m ih]; intros s1 H; cbn in H.
  - inversion H; subst. apply ors_refl.
  - destruct (f s1) as [sm |] eqn:Hf; [| discriminate].
    exact (ors_step f s1 sm s2 Hf (ih sm H)).
Qed.

Lemma iterOpt_reaches_plus (f : State -> option State) (m : nat) (s1 s2 : State) :
  iterOpt f (S m) s1 = Some s2 -> OrbitReachesPlus f s1 s2.
Proof.
  intros H; cbn in H.
  destruct (f s1) as [sm |] eqn:Hf; [| discriminate].
  exact (orp_step f s1 sm s2 Hf (iterOpt_reaches_star f m sm s2 H)).
Qed.

Lemma orbitStar_sound {s1 s2 : State} (h : OrbitReachesStar next s1 s2) :
  encode s1 -->* encode s2.
Proof.
  induction h as [s | s1 s2 s3 hstep _ ih].
  - apply evstep_refl.
  - exact (pev (ps_trans (step_sound hstep) ih)).
Qed.

Lemma orbitPlus_sound {s1 s2 : State} (h : OrbitReachesPlus next s1 s2) :
  encode s1 -->+ encode s2.
Proof.
  destruct h as [s1 s2 s3 hstep hstar].
  exact (ps_trans (step_sound hstep) (orbitStar_sound hstar)).
Qed.

(* Symbolic single-step evaluations of next *)

Lemma next_stA_kpos_c0 (b k : N) (hk : 1 <= k) :
  next (stA b k 0) = Some (stA b (k - 1) 1).
Proof. unfold next. rew_neq k 0. reflexivity. Qed.

Lemma next_stA_b5_k0_c0 (b : N) :
  next (stA (b + 5) 0 0) = Some (stA (b + 1) 0 5).
Proof.
  unfold next.
  rew_neq (b + 5) 0; rew_neq (b + 5) 1; rew_neq (b + 5) 2;
  rew_neq (b + 5) 3; rew_neq (b + 5) 4.
  do 2 f_equal; lia.
Qed.

Lemma next_stA_b1_c1 (k : N) :
  next (stA 1 k 1) = Some (stA (2 * k + 8) 0 3).
Proof. reflexivity. Qed.

Lemma next_stA_b3_c1 (k : N) :
  next (stA 3 k 1) = Some (stA (2 * k + 8) 0 3).
Proof. reflexivity. Qed.

Lemma next_stA_b5_c1 (b k : N) :
  next (stA (b + 5) k 1) = Some (stA (b + 1) 0 (2 * k + 7)).
Proof.
  unfold next.
  rew_neq (b + 5) 0; rew_neq (b + 5) 1; rew_neq (b + 5) 2;
  rew_neq (b + 5) 3; rew_neq (b + 5) 4.
  do 2 f_equal; lia.
Qed.

Lemma next_stA_b1_c2 (k c : N) :
  next (stA 1 k (c + 2)) = Some (stA 1 (k + 2) c).
Proof.
  unfold next.
  rew_neq (c + 2) 0; rew_neq (c + 2) 1.
  do 2 f_equal; lia.
Qed.

Lemma next_stA_b3_c2 (b k c : N) :
  next (stA (b + 3) k (c + 2)) = Some (stA (b + 1) (k + 2) c).
Proof.
  unfold next.
  rew_neq (c + 2) 0; rew_neq (c + 2) 1.
  rew_neq (b + 3) 0; rew_neq (b + 3) 1; rew_neq (b + 3) 2.
  do 2 f_equal; lia.
Qed.

Lemma next_stA_b2_kpos_cpos (k c : N) (hk : 1 <= k) :
  next (stA 2 k (c + 1)) = Some (stOdd 2 0 0 (k - 1) c).
Proof.
  unfold next.
  rew_neq (c + 1) 0; rew_neq k 0.
  destruct (c + 1 =? 1) eqn:Hc; cbn [N.eqb Pos.eqb].
  - apply N.eqb_eq in Hc. do 2 f_equal; lia.
  - apply N.eqb_neq in Hc. do 2 f_equal; lia.
Qed.

Lemma next_stOdd_p0_nsucc (k n m c : N) :
  next (stOdd 0 k (n + 1) m c) = Some (stOdd 0 (k + 2) n m c).
Proof.
  unfold next. rew_neq (n + 1) 0. do 2 f_equal; lia.
Qed.

Lemma next_stOdd_psucc_nsucc (p k n m c : N) :
  next (stOdd (p + 1) k (n + 1) m c) = Some (stOdd p (k + 2) n m c).
Proof.
  unfold next. rew_neq (n + 1) 0; rew_neq (p + 1) 0. do 2 f_equal; lia.
Qed.

Lemma next_stOdd_p0_n0 (k m c : N) :
  next (stOdd 0 k 0 m c) = Some (stETail k m c).
Proof. reflexivity. Qed.

Lemma next_stOdd_p2_n0_m0 (p k c : N) :
  next (stOdd (p + 2) k 0 0 c) = Some (stA (2 * p + 1) 0 (2 * (k + 3) + c)).
Proof.
  unfold next. rew_neq (p + 2) 0; rew_neq (p + 2) 1. do 2 f_equal; lia.
Qed.

Lemma next_stOdd_p2_n0_msucc (p k m c : N) :
  next (stOdd (p + 2) k 0 (m + 1) c) = Some (stOdd p 0 (k + 3) m c).
Proof.
  unfold next. rew_neq (p + 2) 0; rew_neq (p + 2) 1; rew_neq (m + 1) 0.
  do 2 f_equal; lia.
Qed.

Lemma next_stETail_m1 (k c : N) :
  next (stETail k 1 c) = Some (stA (2 * (k + 4) + 1) 0 c).
Proof. reflexivity. Qed.

Lemma next_stETail_m2 (k m c : N) :
  next (stETail k (m + 2) c) = Some (stOdd (k + 4) 0 0 m c).
Proof.
  unfold next. rew_neq (m + 2) 0; rew_neq (m + 2) 1. do 2 f_equal; lia.
Qed.

(* Drain and exponential rules on D1 and Modd *)

Lemma iter_A_drain (j b k c : N) :
  OrbitReachesStar next (stA (b + 2 * j + 1) k (c + 2 * j)) (stA (b + 1) (k + 2 * j) c).
Proof.
  revert k.
  induction j as [| j ih] using N_peano_ind; intros k.
  - replace (b + 2 * 0 + 1) with (b + 1) by lia.
    replace (c + 2 * 0) with c by lia.
    replace (k + 2 * 0) with k by lia.
    apply ors_refl.
  - replace (b + 2 * (j + 1) + 1) with ((b + 2 * j) + 3) by lia.
    replace (c + 2 * (j + 1)) with ((c + 2 * j) + 2) by lia.
    replace (k + 2 * (j + 1)) with ((k + 2) + 2 * j) by lia.
    exact (ors_step next _ _ _ (next_stA_b3_c2 (b + 2 * j) k (c + 2 * j)) (ih (k + 2))).
Qed.

Definition cfg_D1 (a u v : N) : State :=
  if v =? 0 then stA (a - 2) 0 (2 * u + 3)
  else stA a u (v - 1).

Definition cfg_Modd (m u v y z : N) : State :=
  if y =? 0 then cfg_D1 (2 * m + 1) u (v + z)
  else stOdd m u (v / 2) (y - 1) z.

Lemma cfg_D1_zero (a u : N) : cfg_D1 a u 0 = stA (a - 2) 0 (2 * u + 3).
Proof. reflexivity. Qed.

Lemma cfg_D1_pos (a u v : N) (hv : 1 <= v) : cfg_D1 a u v = stA a u (v - 1).
Proof. unfold cfg_D1. rew_neq v 0. reflexivity. Qed.

Lemma cfg_Modd_y0_eq_D1 (m u v z : N) :
  cfg_Modd m u v 0 z = cfg_D1 (2 * m + 1) u (v + z).
Proof. reflexivity. Qed.

Lemma cfg_Modd_ypos (m u v y z : N) (hy : 1 <= y) :
  cfg_Modd m u v y z = stOdd m u (v / 2) (y - 1) z.
Proof. unfold cfg_Modd. rew_neq y 0. reflexivity. Qed.

Lemma drain_D1_v2 (k a u v : N) (hv : 1 <= v) :
  OrbitReachesStar next (cfg_D1 (a + 2 * k + 1) u (v + 2 * k)) (cfg_D1 (a + 1) (u + 2 * k) v).
Proof.
  rewrite (cfg_D1_pos _ _ (v + 2 * k)) by lia.
  rewrite (cfg_D1_pos _ _ v) by lia.
  replace (v + 2 * k - 1) with ((v - 1) + 2 * k) by lia.
  exact (iter_A_drain k a u (v - 1)).
Qed.

Lemma drain_D1_a1_v2 (k u v : N) (hv : 1 <= v) :
  OrbitReachesStar next (cfg_D1 1 u (v + 2 * k)) (cfg_D1 1 (u + 2 * k) v).
Proof.
  revert u.
  induction k as [| k ih] using N_peano_ind; intros u.
  - replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ors_refl.
  - assert (hstep : next (cfg_D1 1 u (v + 2 * (k + 1))) = Some (cfg_D1 1 (u + 2) (v + 2 * k))).
    { rewrite (cfg_D1_pos _ _ (v + 2 * (k + 1))) by lia.
      rewrite (cfg_D1_pos _ _ (v + 2 * k)) by lia.
      replace (v + 2 * (k + 1) - 1) with ((v + 2 * k - 1) + 2) by lia.
      exact (next_stA_b1_c2 u (v + 2 * k - 1)). }
    pose proof (ih (u + 2)) as h2.
    replace ((u + 2) + 2 * k) with (u + 2 * (k + 1)) in h2 by lia.
    exact (ors_step next _ _ _ hstep h2).
Qed.

Lemma accel_D1_double (a u : N) (ha : 2 <= a) :
  OrbitReachesPlus next (cfg_D1 (a + 2 * u + 7) u 0) (cfg_D1 (a + 1) (2 * u + 4) 0).
Proof.
  assert (h_in : cfg_D1 (a + 2 * u + 7) u 0 =
                 cfg_D1 ((a + 2) + 2 * (u + 1) + 1) 0 (2 + 2 * (u + 1))).
  { rewrite cfg_D1_zero, (cfg_D1_pos _ _ (2 + 2 * (u + 1))) by lia.
    f_equal; lia. }
  rewrite h_in.
  pose proof (drain_D1_v2 (u + 1) (a + 2) 0 2 ltac:(lia)) as h1.
  assert (h_step : next (cfg_D1 ((a + 2) + 1) (0 + 2 * (u + 1)) 2) =
                   Some (cfg_D1 (a + 1) (2 * u + 4) 0)).
  { rewrite (cfg_D1_pos _ _ 2) by lia.
    rewrite cfg_D1_zero.
    replace ((a + 2) + 1) with ((a - 2) + 5) by lia.
    replace (2 - 1) with 1 by lia.
    rewrite next_stA_b5_c1.
    do 2 f_equal; lia. }
  exact (ors_trans_plus h1 (orp_single h_step)).
Qed.

Lemma rule_Modd_m0_v2 (u v y z : N) (hv : 1 <= v) :
  OrbitReachesPlus next (cfg_Modd 0 u (v + 2) y z) (cfg_Modd 0 (u + 2) v y z).
Proof.
  destruct (y =? 0) eqn:Hy.
  - apply N.eqb_eq in Hy; subst y.
    rewrite !cfg_Modd_y0_eq_D1.
    rewrite (cfg_D1_pos _ _ (v + 2 + z)) by lia.
    rewrite (cfg_D1_pos _ _ (v + z)) by lia.
    replace (2 * 0 + 1) with 1 by lia.
    replace (v + 2 + z - 1) with ((v + z - 1) + 2) by lia.
    exact (orp_single (next_stA_b1_c2 u (v + z - 1))).
  - apply N.eqb_neq in Hy.
    rewrite !cfg_Modd_ypos by lia.
    replace ((v + 2) / 2) with (v / 2 + 1) by lia.
    exact (orp_single (next_stOdd_p0_nsucc u (v / 2) (y - 1) z)).
Qed.

Lemma rule_Modd_m1_v2 (m u v y z : N) (hv : 1 <= v) :
  OrbitReachesPlus next (cfg_Modd (m + 1) u (v + 2) y z) (cfg_Modd m (u + 2) v y z).
Proof.
  destruct (y =? 0) eqn:Hy.
  - apply N.eqb_eq in Hy; subst y.
    rewrite !cfg_Modd_y0_eq_D1.
    rewrite (cfg_D1_pos _ _ (v + 2 + z)) by lia.
    rewrite (cfg_D1_pos _ _ (v + z)) by lia.
    replace (2 * (m + 1) + 1) with (2 * m + 3) by lia.
    replace (v + 2 + z - 1) with ((v + z - 1) + 2) by lia.
    exact (orp_single (next_stA_b3_c2 (2 * m) u (v + z - 1))).
  - apply N.eqb_neq in Hy.
    rewrite !cfg_Modd_ypos by lia.
    replace ((v + 2) / 2) with (v / 2 + 1) by lia.
    exact (orp_single (next_stOdd_psucc_nsucc m u (v / 2) (y - 1) z)).
Qed.

Lemma rule_Modd_m2_v1 (m u y z : N) :
  OrbitReachesPlus next (cfg_Modd (m + 2) u 1 (y + 1) z) (cfg_Modd m 0 (2 * u + 7) y z).
Proof.
  rewrite (cfg_Modd_ypos _ _ _ (y + 1)) by lia.
  change (1 / 2) with 0.
  replace (y + 1 - 1) with y by lia.
  destruct (y =? 0) eqn:Hy.
  - apply N.eqb_eq in Hy; subst y.
    rewrite cfg_Modd_y0_eq_D1, (cfg_D1_pos _ _ (2 * u + 7 + z)) by lia.
    replace (2 * u + 7 + z - 1) with (2 * (u + 3) + z) by lia.
    exact (orp_single (next_stOdd_p2_n0_m0 m u z)).
  - apply N.eqb_neq in Hy.
    rewrite (cfg_Modd_ypos _ _ _ y) by lia.
    replace ((2 * u + 7) / 2) with (u + 3) by lia.
    replace y with ((y - 1) + 1) at 1 by lia.
    exact (orp_single (next_stOdd_p2_n0_msucc m u (y - 1) z)).
Qed.

Lemma rule_Modd_m0_v1_y2 (u y z : N) :
  OrbitReachesPlus next (cfg_Modd 0 u 1 (y + 2) z) (cfg_Modd (u + 4) 0 1 y z).
Proof.
  rewrite (cfg_Modd_ypos _ _ _ (y + 2)) by lia.
  change (1 / 2) with 0.
  replace (y + 2 - 1) with (y + 1) by lia.
  pose proof (next_stOdd_p0_n0 u (y + 1) z) as h1.
  destruct (y =? 0) eqn:Hy.
  - apply N.eqb_eq in Hy; subst y.
    rewrite cfg_Modd_y0_eq_D1, (cfg_D1_pos _ _ (1 + z)) by lia.
    replace (1 + z - 1) with z by lia.
    change (0 + 1) with 1 in h1.
    exact (orp_step2 h1 (next_stETail_m1 u z)).
  - apply N.eqb_neq in Hy.
    rewrite (cfg_Modd_ypos _ _ _ y) by lia.
    change (1 / 2) with 0.
    pose proof (next_stETail_m2 u (y - 1) z) as h2.
    replace ((y - 1) + 2) with (y + 1) in h2 by lia.
    exact (orp_step2 h1 h2).
Qed.

Lemma drain_Modd_v2 (k m u v y z : N) (hv : 1 <= v) :
  OrbitReachesStar next (cfg_Modd (m + k) u (v + 2 * k) y z) (cfg_Modd m (u + 2 * k) v y z).
Proof.
  revert m u v hv.
  induction k as [| k ih] using N_peano_ind; intros m u v hv.
  - replace (m + 0) with m by lia.
    replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ors_refl.
  - replace (m + (k + 1)) with ((m + k) + 1) by lia.
    replace (v + 2 * (k + 1)) with ((v + 2 * k) + 2) by lia.
    pose proof (rule_Modd_m1_v2 (m + k) u (v + 2 * k) y z ltac:(lia)) as hstep.
    pose proof (ih m (u + 2) v hv) as hrest.
    replace ((u + 2) + 2 * k) with (u + 2 * (k + 1)) in hrest by lia.
    exact (orp_to_star (orp_trans_star hstep hrest)).
Qed.

Lemma drain_Modd_m0_v2 (k u v y z : N) (hv : 1 <= v) :
  OrbitReachesStar next (cfg_Modd 0 u (v + 2 * k) y z) (cfg_Modd 0 (u + 2 * k) v y z).
Proof.
  revert u v hv.
  induction k as [| k ih] using N_peano_ind; intros u v hv.
  - replace (v + 2 * 0) with v by lia.
    replace (u + 2 * 0) with u by lia.
    apply ors_refl.
  - replace (v + 2 * (k + 1)) with ((v + 2 * k) + 2) by lia.
    pose proof (rule_Modd_m0_v2 u (v + 2 * k) y z ltac:(lia)) as h1.
    pose proof (ih (u + 2) v hv) as h2.
    replace ((u + 2) + 2 * k) with (u + 2 * (k + 1)) in h2 by lia.
    exact (orp_to_star (orp_trans_star h1 h2)).
Qed.

Lemma mul_pow2_ge (k n : N) : k <= k * 2 ^ n.
Proof.
  induction n as [| n ih] using N_peano_ind.
  - change (2 ^ 0) with 1; lia.
  - rewrite pow2_succ; lia.
Qed.

Lemma pow2_mono {a b : N} (h : a <= b) : 2 ^ a <= 2 ^ b.
Proof.
  replace b with (a + (b - a)) by lia.
  rewrite pow2_add.
  exact (mul_pow2_ge (2 ^ a) (b - a)).
Qed.

Lemma pow2_ge_two_mul (n : N) (hn : 5 <= n) : 2 * n + 6 <= 2 ^ n.
Proof.
  set (d := n - 5).
  replace n with (d + 5) by lia.
  clear hn; subst d.
   generalize (n - 5); clear n; intros d.
  induction d as [| d ih] using N_peano_ind.
  - vm_compute; discriminate.
  - replace (d + 1 + 5) with ((d + 5) + 1) by lia.
    rewrite pow2_succ; lia.
Qed.

Lemma pow2_ge_four_mul (n : N) (hn : 6 <= n) : 4 * n + 16 <= 2 ^ n.
Proof.
  replace n with ((n - 6) + 6) by lia.
  generalize (n - 6); clear n hn; intros d.
  induction d as [| d ih] using N_peano_ind.
  - vm_compute; discriminate.
  - replace (d + 1 + 6) with ((d + 6) + 1) by lia.
    rewrite pow2_succ; lia.
Qed.

Lemma mul_pow2_ge_linear (u n : N) :
  2 * (u + 4) + 2 * n <= 2 * (u + 4) * 2 ^ n.
Proof.
  induction n as [| n ih] using N_peano_ind.
  - change (2 ^ 0) with 1; lia.
  - pose proof (mul_pow2_ge (u + 4) n) as h1.
    rewrite pow2_succ; nia.
Qed.

Lemma exp_step_D1_exact (n a u : N) (ha : 2 <= a) :
  OrbitReachesStar next
    (cfg_D1 (a + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1) u 0)
    (cfg_D1 (a + 1) ((u + 4) * 2 ^ n - 4) 0).
Proof.
  revert a u ha.
  induction n as [| n ih] using N_peano_ind; intros a u ha.
  - change (2 ^ 0) with 1.
    replace (a + (2 * (u + 4) * 1 - 2 * (u + 4) - 2 * 0) + 1) with (a + 1) by lia.
    replace ((u + 4) * 1 - 4) with u by lia.
    apply ors_refl.
  - set (k := (u + 4) * 2 ^ n).
    assert (hk : u + 4 <= k) by (unfold k; exact (mul_pow2_ge (u + 4) n)).
    assert (h2k : 2 * (u + 4) * 2 ^ n = 2 * k) by (unfold k; lia).
    assert (hlin : 2 * (u + 4) + 2 * n <= 2 * k).
    { rewrite <- h2k. exact (mul_pow2_ge_linear u n). }
    assert (hpow : 2 * (u + 4) * 2 ^ (n + 1) = 4 * k).
    { unfold k. rewrite pow2_succ; lia. }
    assert (ha_in : a + (2 * (u + 4) * 2 ^ (n + 1) - 2 * (u + 4) - 2 * (n + 1)) + 1 =
                    (a + 2 * (k - 4) + 6) + (2 * (u + 4) * 2 ^ n - 2 * (u + 4) - 2 * n) + 1).
    { rewrite hpow, h2k. clear - hk hlin; lia. }
    rewrite ha_in.
    pose proof (ih (a + 2 * (k - 4) + 6) u ltac:(lia)) as h1.
    replace ((a + 2 * (k - 4) + 6) + 1) with (a + 2 * (k - 4) + 7) in h1 by lia.
    pose proof (accel_D1_double a (k - 4) ha) as h2.
    assert (hu_out : 2 * (k - 4) + 4 = (u + 4) * 2 ^ (n + 1) - 4).
    { assert (hk2 : (u + 4) * 2 ^ (n + 1) = 2 * k) by (unfold k; rewrite pow2_succ; lia).
      rewrite hk2. clear - hk; lia. }
    rewrite hu_out in h2.
    exact (ors_trans h1 (orp_to_star h2)).
Qed.

Lemma enter_Modd_from_D1 (k u z : N) (hk : 1 <= k) (hz : 2 * u + 2 = 2 * k + z) :
  OrbitReachesPlus next (cfg_D1 (2 * k + 4) u 0) (cfg_Modd 2 0 1 (2 * k) z).
Proof.
  assert (h_in : cfg_D1 (2 * k + 4) u 0 = cfg_D1 (1 + 2 * k + 1) 0 ((z + 2) + 2 * k)).
  { rewrite cfg_D1_zero, (cfg_D1_pos _ _ ((z + 2) + 2 * k)) by lia.
    f_equal; lia. }
  rewrite h_in.
  pose proof (drain_D1_v2 k 1 0 (z + 2) ltac:(lia)) as h1.
  assert (h_step : next (cfg_D1 (1 + 1) (0 + 2 * k) (z + 2)) = Some (cfg_Modd 2 0 1 (2 * k) z)).
  { rewrite (cfg_D1_pos _ _ (z + 2)) by lia.
    rewrite (cfg_Modd_ypos _ _ _ (2 * k)) by lia.
    change (1 + 1) with 2; change (1 / 2) with 0.
    replace (0 + 2 * k) with (2 * k) by lia.
    replace (z + 2 - 1) with (z + 1) by lia.
    exact (next_stA_b2_kpos_cpos (2 * k) z ltac:(lia)). }
  exact (ors_trans_plus h1 (orp_single h_step)).
Qed.

Lemma accel_Modd_double (m u y z : N) :
  OrbitReachesPlus next (cfg_Modd (m + u + 5) u 1 (y + 1) z) (cfg_Modd m (2 * u + 6) 1 y z).
Proof.
  replace (m + u + 5) with ((m + (u + 3)) + 2) by lia.
  pose proof (rule_Modd_m2_v1 (m + (u + 3)) u y z) as h1.
  replace (2 * u + 7) with (1 + 2 * (u + 3)) in h1 by lia.
  pose proof (drain_Modd_v2 (u + 3) m 0 1 y z ltac:(lia)) as h2.
  replace (0 + 2 * (u + 3)) with (2 * u + 6) in h2 by lia.
  exact (orp_trans_star h1 h2).
Qed.

Lemma six_pow2_ge_linear (e : N) : e + 6 <= 6 * 2 ^ e.
Proof.
  induction e as [| e ih] using N_peano_ind.
  - change (2 ^ 0) with 1; lia.
  - rewrite pow2_succ; lia.
Qed.

Lemma exp_step_Modd_exact (e m y z : N) :
  OrbitReachesStar next
    (cfg_Modd (m + (6 * 2 ^ e - 6 - e)) 0 1 (y + e) z)
    (cfg_Modd m (6 * 2 ^ e - 6) 1 y z).
Proof.
  revert m y.
  induction e as [| e ih] using N_peano_ind; intros m y.
  - change (2 ^ 0) with 1.
    replace (m + (6 * 1 - 6 - 0)) with m by lia.
    replace (y + 0) with y by lia.
    replace (6 * 1 - 6) with 0 by lia.
    apply ors_refl.
  - set (k := 6 * 2 ^ e).
    assert (hk : e + 6 <= k) by (unfold k; exact (six_pow2_ge_linear e)).
    assert (hpow : 6 * 2 ^ (e + 1) = 2 * k) by (unfold k; rewrite pow2_succ; lia).
    assert (hm_in : m + (6 * 2 ^ (e + 1) - 6 - (e + 1)) =
                    (m + (k - 6) + 5) + (k - 6 - e)).
    { rewrite hpow. clear - hk; lia. }
    assert (hy_in : y + (e + 1) = (y + 1) + e) by lia.
    rewrite hm_in, hy_in.
    pose proof (ih (m + (k - 6) + 5) (y + 1)) as h1.
    pose proof (accel_Modd_double m (k - 6) y z) as h2.
    assert (hu_out : 2 * (k - 6) + 6 = 6 * 2 ^ (e + 1) - 6).
    { rewrite hpow. clear - hk; lia. }
    rewrite hu_out in h2.
    exact (ors_trans h1 (orp_to_star h2)).
Qed.

Lemma finish_pass_Modd (m u y z : N) (hm : m <= u + 3) :
  OrbitReachesPlus next (cfg_Modd (m + 2) u 1 (y + 3) z) (cfg_Modd (2 * u + 10) 0 1 y z).
Proof.
  replace (y + 3) with ((y + 2) + 1) by lia.
  pose proof (rule_Modd_m2_v1 m u (y + 2) z) as h1.
  pose proof (drain_Modd_v2 m 0 0 (1 + 2 * (u + 3 - m)) (y + 2) z ltac:(lia)) as h2.
  replace (0 + m) with m in h2 by lia.
  replace ((1 + 2 * (u + 3 - m)) + 2 * m) with (2 * u + 7) in h2 by lia.
  pose proof (orp_trans_star h1 h2) as h12.
  pose proof (drain_Modd_m0_v2 (u + 3 - m) (0 + 2 * m) 1 (y + 2) z ltac:(lia)) as h3.
  pose proof (orp_trans_star h12 h3) as h123.
  replace (0 + 2 * m + 2 * (u + 3 - m)) with (2 * u + 6) in h123 by lia.
  pose proof (rule_Modd_m0_v1_y2 (2 * u + 6) y z) as h4.
  replace ((2 * u + 6) + 4) with (2 * u + 10) in h4 by lia.
  exact (orp_trans h123 h4).
Qed.

Lemma pass0_Modd (y z : N) :
  OrbitReachesPlus next (cfg_Modd 2 0 1 (y + 3) z) (cfg_Modd 10 0 1 y z).
Proof. exact (finish_pass_Modd 0 0 y z ltac:(lia)). Qed.

Lemma single_pass_Modd_pos (e y z : N) :
  OrbitReachesPlus next
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
  { rewrite pow2_succ; lia. }
  rewrite hu_out in h2.
  exact (ors_trans_plus h1 h2).
Qed.

Lemma tri_succ (e : N) :
  (e + 1) * (e + 6) / 2 = e * (e + 5) / 2 + (e + 3).
Proof.
  replace ((e + 1) * (e + 6)) with (e * (e + 5) + (e + 3) * 2) by nia.
  apply N.div_add. lia.
Qed.

Lemma two_mul_tri (E : N) : 2 * (E * (E + 5) / 2) = E * (E + 5).
Proof.
  induction E as [| e ih] using N_peano_ind.
  - reflexivity.
  - replace (e + 1 + 5) with (e + 6) by lia.
    rewrite tri_succ; nia.
Qed.

Lemma multi_pass_Modd_pos (E y z : N) (hE : 1 <= E) :
  OrbitReachesPlus next
    (cfg_Modd 2 0 1 (y + E * (E + 5) / 2) z)
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z).
Proof.
  replace E with ((E - 1) + 1) by lia.
  generalize (E - 1); clear E hE; intros d.
  revert y.
  induction d as [| d ih] using N_peano_ind; intros y.
  - change (0 + 1) with 1; change (1 * (1 + 5) / 2) with 3; change (6 * 2 ^ 1 - 2) with 10.
    exact (pass0_Modd y z).
  - pose proof (tri_succ (d + 1)) as htri.
    replace (d + 1 + 1 + 5) with (d + 1 + 6) by lia.
    rewrite htri.
    replace (y + ((d + 1) * (d + 1 + 5) / 2 + (d + 1 + 3)))
      with ((y + (d + 1) + 3) + (d + 1) * (d + 1 + 5) / 2) by lia.
    exact (orp_trans (ih (y + (d + 1) + 3)) (single_pass_Modd_pos (d + 1) y z)).
Qed.

Lemma exit_Modd_y1 (E z : N) :
  OrbitReachesPlus next
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 1 z)
    (cfg_D1 (12 * 2 ^ E - 7) 0 (z + 7)).
Proof.
  pose proof (six_pow2_ge_linear E) as hk.
  replace (6 * 2 ^ E - 2) with ((6 * 2 ^ E - 4) + 2) by lia.
  change 1 with (0 + 1) at 2.
  pose proof (rule_Modd_m2_v1 (6 * 2 ^ E - 4) 0 0 z) as h1.
  rewrite cfg_Modd_y0_eq_D1 in h1.
  replace (2 * (6 * 2 ^ E - 4) + 1) with (12 * 2 ^ E - 7) in h1 by lia.
  replace (2 * 0 + 7 + z) with (z + 7) in h1 by lia.
  exact h1.
Qed.

Lemma exit_Modd_mid (E y z : N) (hy1 : 2 <= y) (hy2 : y <= E + 1) :
  OrbitReachesPlus next
    (cfg_Modd (6 * 2 ^ E - 2) 0 1 y z)
    (cfg_D1 (12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3) 0 (12 * 2 ^ (y - 1) + z - 5)).
Proof.
  set (r := y - 1).
  assert (hrE : r <= E) by (unfold r; lia).
  assert (hpow_ge : 6 * 2 ^ r <= 6 * 2 ^ E).
  { pose proof (pow2_mono hrE); lia. }
  pose proof (six_pow2_ge_linear r) as hlin_r.
  set (m_rem := 6 * 2 ^ E - 6 * 2 ^ r + r + 4).
  pose proof (exp_step_Modd_exact r m_rem 1 z) as h1.
  assert (hm_in : m_rem + (6 * 2 ^ r - 6 - r) = 6 * 2 ^ E - 2) by (unfold m_rem; lia).
  assert (hy_in : 1 + r = y) by (unfold r; lia).
  rewrite hm_in, hy_in in h1.
  assert (hm_mid : m_rem = (m_rem - 2) + 2) by (unfold m_rem; lia).
  rewrite hm_mid in h1.
  pose proof (rule_Modd_m2_v1 (m_rem - 2) (6 * 2 ^ r - 6) 0 z) as h2.
  rewrite cfg_Modd_y0_eq_D1 in h2.
  assert (ha_out : 2 * (m_rem - 2) + 1 = 12 * 2 ^ E - 12 * 2 ^ (y - 1) + 2 * y + 3).
  { unfold m_rem, r in *; clear h1 h2 hm_in hy_in hm_mid; lia. }
  assert (hv_out : 2 * (6 * 2 ^ r - 6) + 7 + z = 12 * 2 ^ (y - 1) + z - 5).
  { unfold r in *; clear - hlin_r; lia. }
  rewrite ha_out, hv_out in h2.
  exact (ors_trans_plus h1 h2).
Qed.

Lemma odd_v1_ge_a1_reload (m kv : N) (h : m <= kv) :
  OrbitReachesPlus next (cfg_D1 (2 * m + 1) 0 (2 * kv + 1)) (cfg_D1 (4 * kv + 8) 0 0).
Proof.
  pose proof (drain_D1_v2 m 0 0 (1 + 2 * (kv - m)) ltac:(lia)) as h1.
  replace (0 + 2 * m + 1) with (2 * m + 1) in h1 by lia.
  replace ((1 + 2 * (kv - m)) + 2 * m) with (2 * kv + 1) in h1 by lia.
  change (0 + 1) with 1 in h1.
  pose proof (drain_D1_a1_v2 (kv - m) (0 + 2 * m) 1 ltac:(lia)) as h2.
  pose proof (ors_trans h1 h2) as h12.
  replace (0 + 2 * m + 2 * (kv - m)) with (2 * kv) in h12 by lia.
  assert (h3 : OrbitReachesPlus next (cfg_D1 1 (2 * kv) 1) (cfg_D1 (4 * kv + 8) 0 0)).
  { destruct (kv =? 0) eqn:Hkv.
    - apply N.eqb_eq in Hkv; subst kv.
      apply orp_single. vm_compute. reflexivity.
    - apply N.eqb_neq in Hkv.
      rewrite (cfg_D1_pos 1 (2 * kv) 1) by lia.
      rewrite cfg_D1_zero.
      change (1 - 1) with 0.
      pose proof (next_stA_kpos_c0 1 (2 * kv) ltac:(lia)) as hs1.
      pose proof (next_stA_b1_c1 (2 * kv - 1)) as hs2.
      replace (2 * (2 * kv - 1) + 8) with (4 * kv + 8 - 2) in hs2 by (clear - Hkv; lia).
      exact (orp_step2 hs1 hs2). }
  exact (ors_trans_plus h12 h3).
Qed.

Lemma odd_drain_v1 (ma kv : N) (hma : 1 <= ma) :
  OrbitReachesPlus next
    (cfg_D1 (2 * ma + 2 * kv + 3) 0 (2 * kv + 1))
    (cfg_D1 (2 * ma + 1) (2 * kv + 1) 0).
Proof.
  pose proof (drain_D1_v2 kv (2 * ma + 2) 0 1 ltac:(lia)) as h1.
  replace ((2 * ma + 2) + 2 * kv + 1) with (2 * ma + 2 * kv + 3) in h1 by lia.
  replace (1 + 2 * kv) with (2 * kv + 1) in h1 by lia.
  replace ((2 * ma + 2) + 1) with (2 * ma + 3) in h1 by lia.
  replace (0 + 2 * kv) with (2 * kv) in h1 by lia.
  assert (h2 : OrbitReachesPlus next
                 (cfg_D1 (2 * ma + 3) (2 * kv) 1)
                 (cfg_D1 (2 * ma + 1) (2 * kv + 1) 0)).
  { rewrite (cfg_D1_pos _ _ 1) by lia.
    rewrite cfg_D1_zero; change (1 - 1) with 0.
    destruct (kv =? 0) eqn:Hkv.
    - apply N.eqb_eq in Hkv; subst kv.
      replace (2 * ma + 3) with ((2 * ma - 2) + 5) by lia.
      replace (2 * ma + 1 - 2) with ((2 * ma - 2) + 1) by lia.
      change (2 * 0) with 0; change (2 * (0 + 1) + 3) with 5.
      exact (orp_single (next_stA_b5_k0_c0 (2 * ma - 2))).
    - apply N.eqb_neq in Hkv.
      pose proof (next_stA_kpos_c0 (2 * ma + 3) (2 * kv) ltac:(lia)) as hs1.
      replace (2 * ma + 3) with ((2 * ma - 2) + 5) in hs1 |- * by lia.
      pose proof (next_stA_b5_c1 (2 * ma - 2) (2 * kv - 1)) as hs2.
      replace ((2 * ma - 2) + 1) with (2 * ma + 1 - 2) in hs2 by lia.
      replace (2 * (2 * kv - 1) + 7) with (2 * (2 * kv + 1) + 3) in hs2 by (clear - Hkv; lia).
      exact (orp_step2 hs1 hs2). }
  exact (ors_trans_plus h1 h2).
Qed.

Lemma odd_rem_ge3_reload (m u : N) (hm : m <= u + 2) :
  OrbitReachesPlus next (cfg_D1 (2 * m + 3) u 0) (cfg_D1 (4 * u + 14) 0 0).
Proof.
  assert (h_in : cfg_D1 (2 * m + 3) u 0 = cfg_D1 (2 * m + 1) 0 (2 * u + 4)).
  { rewrite cfg_D1_zero, (cfg_D1_pos _ _ (2 * u + 4)) by lia.
    f_equal; lia. }
  rewrite h_in.
  assert (h_cases : m = u + 2 \/ m <= u + 1) by lia.
  destruct h_cases as [-> | hm1].
  - pose proof (drain_D1_v2 (u + 1) 2 0 2 ltac:(lia)) as h1.
    replace (2 + 2 * (u + 1) + 1) with (2 * (u + 2) + 1) in h1 by lia.
    replace (2 + 2 * (u + 1)) with (2 * u + 4) in h1 by lia.
    change (2 + 1) with 3 in h1.
    replace (0 + 2 * (u + 1)) with (2 * u + 2) in h1 by lia.
    assert (h2 : next (cfg_D1 3 (2 * u + 2) 2) = Some (cfg_D1 (4 * u + 14) 0 0)).
    { rewrite (cfg_D1_pos _ _ 2) by lia; rewrite cfg_D1_zero; change (2 - 1) with 1.
      rewrite next_stA_b3_c1. do 2 f_equal; lia. }
    exact (ors_trans_plus h1 (orp_single h2)).
  - pose proof (drain_D1_v2 m 0 0 (2 + 2 * (u + 1 - m)) ltac:(lia)) as h1.
    replace (0 + 2 * m + 1) with (2 * m + 1) in h1 by lia.
    replace ((2 + 2 * (u + 1 - m)) + 2 * m) with (2 * u + 4) in h1 by lia.
    change (0 + 1) with 1 in h1.
    pose proof (drain_D1_a1_v2 (u + 1 - m) (0 + 2 * m) 2 ltac:(lia)) as h2.
    pose proof (ors_trans h1 h2) as h12.
    replace (0 + 2 * m + 2 * (u + 1 - m)) with (2 * u + 2) in h12 by lia.
    assert (h3 : next (cfg_D1 1 (2 * u + 2) 2) = Some (cfg_D1 (4 * u + 14) 0 0)).
    { rewrite (cfg_D1_pos _ _ 2) by lia; rewrite cfg_D1_zero; change (2 - 1) with 1.
      rewrite next_stA_b1_c1. do 2 f_equal; lia. }
    exact (ors_trans_plus h12 (orp_single h3)).
Qed.

Lemma era_mid_ge3_step (a0 n k0 z E y ma kv r m_rem2 A_next : N)
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
  OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by lia.
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by lia.
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ors_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  assert (hy_split : 2 * k0 = y + E * (E + 5) / 2) by (clear - hy0 htri; lia).
  rewrite hy_split in h12.
  pose proof (multi_pass_Modd_pos E y z hE) as h3.
  pose proof (orp_trans h12 h3) as h123.
  pose proof (exit_Modd_mid E y z hy1 hy2) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (orp_trans h123 h4) as h1234.
  assert (hma_pos : 1 <= ma) by (clear - ha2; lia).
  pose proof (odd_drain_v1 ma kv hma_pos) as h5.
  pose proof (orp_trans h1234 h5) as h12345.
  rewrite ha2 in h12345.
  pose proof (exp_step_D1_exact r (2 * m_rem2 + 2) (2 * kv + 1) ltac:(lia)) as h6.
  replace (2 * kv + 1 + 4) with (2 * kv + 5) in h6 by lia.
  replace ((2 * m_rem2 + 2) + 1) with (2 * m_rem2 + 3) in h6 by lia.
  pose proof (orp_trans_star h12345 h6) as h123456.
  assert (hm2_bound : m_rem2 <= ((2 * kv + 5) * 2 ^ r - 4) + 2) by (clear - hm2; lia).
  pose proof (odd_rem_ge3_reload m_rem2 ((2 * kv + 5) * 2 ^ r - 4) hm2_bound) as h7.
  rewrite <- hAnext in h7.
  exact (orp_trans h123456 h7).
Qed.

Lemma era_mid_v1_ge_a1_step (a0 n k0 z E y m kv A_next : N)
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
  OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by lia.
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by lia.
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ors_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  assert (hy_split : 2 * k0 = y + E * (E + 5) / 2) by (clear - hy0 htri; lia).
  rewrite hy_split in h12.
  pose proof (multi_pass_Modd_pos E y z hE) as h3.
  pose proof (orp_trans h12 h3) as h123.
  pose proof (exit_Modd_mid E y z hy1 hy2) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (orp_trans h123 h4) as h1234.
  pose proof (odd_v1_ge_a1_reload m kv hm) as h5.
  rewrite <- hAnext in h5.
  exact (orp_trans h1234 h5).
Qed.

Lemma era_y1_v1_ge_a1_step (a0 n k0 z E m kv A_next : N)
    (hA : a0 = (2 * k0 + 3) + (8 * 2 ^ n - 8 - 2 * n) + 1)
    (hk0 : 1 <= k0)
    (hz : 2 * (4 * 2 ^ n - 4) + 2 = 2 * k0 + z)
    (hE : 1 <= E)
    (hy0 : 2 * (2 * k0) = E * (E + 5) + 2)
    (ha1 : 12 * 2 ^ E - 7 = 2 * m + 1)
    (hv1 : z + 7 = 2 * kv + 1)
    (hm : m <= kv)
    (hAnext : A_next = 4 * kv + 8) :
  OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  pose proof (exp_step_D1_exact n (2 * k0 + 3) 0 ltac:(lia)) as h1.
  replace ((2 * k0 + 3) + (2 * (0 + 4) * 2 ^ n - 2 * (0 + 4) - 2 * n) + 1)
    with a0 in h1 by (clear - hA; lia).
  replace ((2 * k0 + 3) + 1) with (2 * k0 + 4) in h1 by lia.
  replace ((0 + 4) * 2 ^ n - 4) with (4 * 2 ^ n - 4) in h1 by lia.
  pose proof (enter_Modd_from_D1 k0 (4 * 2 ^ n - 4) z hk0 hz) as h2.
  pose proof (ors_trans_plus h1 h2) as h12.
  pose proof (two_mul_tri E) as htri.
  assert (hy_split : 2 * k0 = 1 + E * (E + 5) / 2) by (clear - hy0 htri; lia).
  rewrite hy_split in h12.
  pose proof (multi_pass_Modd_pos E 1 z hE) as h3.
  pose proof (orp_trans h12 h3) as h123.
  pose proof (exit_Modd_y1 E z) as h4.
  rewrite ha1, hv1 in h4.
  pose proof (orp_trans h123 h4) as h1234.
  pose proof (odd_v1_ge_a1_reload m kv hm) as h5.
  rewrite <- hAnext in h5.
  exact (orp_trans h1234 h5).
Qed.

(* ========================================================================== *)
(* Layer 3: Concrete Eras 1-10, Sub-Tower Invariant, and Non-Halting Theorem  *)
(* ========================================================================== *)

Lemma sq_sub3_add2 (a0 : N) (hA : 3 <= a0) :
  (a0 - 3) * (a0 + 2) + a0 + 6 = a0 * a0.
Proof.
  replace a0 with ((a0 - 3) + 3) by lia.
  generalize (a0 - 3); intros d; clear; nia.
Qed.

Lemma sq_add (a b : N) :
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b.
Proof. nia. Qed.

Lemma sq_sub (X Y : N) (h : Y <= X) :
  (X - Y) * (X - Y) + 2 * (X * Y) = X * X + Y * Y.
Proof.
  replace X with ((X - Y) + Y) by lia.
  generalize (X - Y); intros d; clear; nia.
Qed.

Lemma mul_coef (c1 c2 x y : N) :
  (c1 * x) * (c2 * y) = (c1 * c2) * (x * y).
Proof. nia. Qed.

Ltac N_decide := vm_compute; try reflexivity; discriminate.

Lemma era1 : OrbitReachesPlus next start (cfg_D1 62 0 0).
Proof. apply (iterOpt_reaches_plus next 34). vm_compute. reflexivity. Qed.

Lemma era2 : OrbitReachesPlus next (cfg_D1 62 0 0) (cfg_D1 120 0 0).
Proof.
  apply (era_y1_v1_ge_a1_step 62 3 4 50 2 20 28 120); N_decide.
Qed.

Lemma era3 : OrbitReachesPlus next (cfg_D1 120 0 0) (cfg_D1 256 0 0).
Proof.
  apply (era_y1_v1_ge_a1_step 120 4 2 118 1 8 62 256); N_decide.
Qed.

Lemma era4 : OrbitReachesPlus next (cfg_D1 256 0 0) (cfg_D1 516 0 0).
Proof.
  apply (era_mid_v1_ge_a1_step 256 5 7 236 3 2 39 127 516); N_decide.
Qed.

Lemma era5 : OrbitReachesPlus next (cfg_D1 516 0 0) (cfg_D1 1016 0 0).
Proof.
  apply (era_mid_v1_ge_a1_step 516 6 10 486 4 2 87 252 1016); N_decide.
Qed.

Lemma era6 : OrbitReachesPlus next (cfg_D1 1016 0 0) (cfg_D1 2108 0 0).
Proof.
  apply (era_mid_v1_ge_a1_step 1016 7 5 1008 2 3 4 525 2108); N_decide.
Qed.

Lemma era7 : OrbitReachesPlus next (cfg_D1 2108 0 0) (cfg_D1 17222 0 0).
Proof.
  apply (era_mid_ge3_step 2108 8 40 1962 10 5 4979 1074 1 2826 17222); N_decide.
Qed.

Lemma era8 : OrbitReachesPlus next (cfg_D1 17222 0 0) (cfg_D1 8534636888062 0 0).
Proof.
  apply (era_mid_ge3_step 17222 11 432 15514 39 6 3298534875196 7946 27 1164875669103 8534636888062); N_decide.
Qed.

Definition A10_gen (p0_exp s_exp : N) : N :=
  12 * 2 ^ (p0_exp + p0_exp + 1) + 2 * (522912268114 * 2 ^ s_exp) * 2 ^ (p0_exp + 2) - 2.

Lemma era9_core (p0_exp s_exp y91 r9 E9 y9 Q R QR kv ma m_rem2 A_next : N)
    (hp0 : p0_exp = 1438155) (hs : s_exp = 736251) (hy91 : y91 = 701901)
    (hr9 : r9 = s_exp + (p0_exp + 2))
    (hE9 : E9 = p0_exp + p0_exp + 1)
    (hy9 : y9 = y91 + 1)
    (hQ : Q = 2 ^ y91)
    (hR : R = 2 ^ r9)
    (hQR_def : QR = Q * R)
    (hkv : kv = 6 * Q + 130728067026)
    (hma : ma = 24 * QR - 12 * Q - 130727365124)
    (hm_rem2 : m_rem2 = 12 * QR - 261456134057 * R + 130730943340)
    (hAnext : A_next = A10_gen p0_exp s_exp) :
  OrbitReachesPlus next (cfg_D1 8534636888062 0 0) (cfg_D1 A_next 0 0).
Proof.
  assert (hQR : 2 ^ E9 = 4 * QR).
  { assert (hsub : E9 = y91 + r9 + 2) by (clear - hp0 hs hy91 hr9 hE9; lia).
    rewrite hsub, !pow2_add, <- hQ, <- hR.
    change (2 ^ 2) with 4. clear - hQR_def; nia. }
  assert (hQ_ge : 261456134058 <= Q).
  { assert (h1 : 2 ^ 39 <= Q) by (rewrite hQ; apply pow2_mono; clear - hy91; lia).
    assert (h2 : 261456134058 <= 2 ^ 39) by N_decide.
    clear - h1 h2; lia. }
  assert (hR_ge : 2 <= R).
  { assert (h1 : 2 ^ 1 <= R) by (rewrite hR; apply pow2_mono; clear - hp0 hs hr9; lia).
    change (2 ^ 1) with 2 in h1; exact h1. }
  assert (hQR_ge : 2 * Q <= QR) by (clear - hQR_def hR_ge; nia).
  assert (h6QR_ge : 261456134057 * R <= 6 * QR) by (clear - hQR_def hQ_ge; nia).
  assert (hkv5 : 2 * kv + 5 = 12 * Q + 261456134057) by (clear - hkv; lia).
  assert (hkvR : (2 * kv + 5) * R = 12 * QR + 261456134057 * R) by (clear - hkv5 hQR_def; nia).
  apply (era_mid_ge3_step 8534636888062 39 2068295188520 261456134058 E9 y9
           ma kv r9 m_rem2 A_next).
  - N_decide.
  - N_decide.
  - N_decide.
  - clear - hp0 hE9; lia.
  - rewrite hE9, hp0, hy9, hy91. N_decide.
  - clear - hy91 hy9; lia.
  - clear - hp0 hy91 hE9 hy9; lia.
  - replace (y9 - 1) with y91 by (clear - hy9; lia).
    rewrite hQR, <- hQ.
    clear - hy91 hy9 hQ_ge hQR_ge hkv hma; lia.
  - replace (y9 - 1) with y91 by (clear - hy9; lia).
    rewrite <- hQ. clear - hkv; lia.
  - rewrite <- hR.
    assert (h2kvR : 2 * (2 * kv + 5) * R = 2 * (12 * QR + 261456134057 * R))
      by (clear - hkvR; lia).
    rewrite h2kvR, hkv5.
    clear - hp0 hs hr9 hQ_ge hR_ge hQR_ge h6QR_ge hma hm_rem2; lia.
  - rewrite <- hR, hkvR.
    clear - hp0 hs hr9 hR_ge h6QR_ge hm_rem2; lia.
  - rewrite hAnext; unfold A10_gen.
    rewrite <- hR, hkvR.
    assert (hE9_pow : 2 ^ (p0_exp + p0_exp + 1) = 4 * QR) by (rewrite <- hE9; exact hQR).
    assert (hpow_r9 : 2 ^ s_exp * 2 ^ (p0_exp + 2) = R)
      by (rewrite <- pow2_add, <- hr9; symmetry; exact hR).
    assert (hR_split : 2 * (522912268114 * 2 ^ s_exp) * 2 ^ (p0_exp + 2) = 4 * (261456134057 * R))
      by (clear - hpow_r9; nia).
    rewrite hE9_pow, hR_split.
    clear - hQ_ge hR_ge hQR_ge; lia.
Qed.

Lemma era9_gen (p0_exp s_exp y91 : N)
    (hp0 : p0_exp = 1438155) (hs : s_exp = 736251) (hy91 : y91 = 701901) :
  OrbitReachesPlus next (cfg_D1 8534636888062 0 0) (cfg_D1 (A10_gen p0_exp s_exp) 0 0).
Proof.
  eapply era9_core; [exact hp0 | exact hs | exact hy91 | reflexivity ..].
Qed.

Definition A_SubTower (M K : N) : N :=
  12 * 2 ^ (2 * M - 3) + 4 * K - 2.

Definition cfg_SubTower (M K : N) : State :=
  cfg_D1 (A_SubTower M K) 0 0.

Definition SubTowerInv (M K : N) : Prop :=
  128 <= M /\ 2 <= K /\ 4 * K + 4 * M + 4 <= 2 ^ (M - 2).

Lemma era10_hy0_poly (P0 S D0 SD0 D02 P02 P0S X Y E : N)
    (hD02 : D02 = D0 * D0)
    (hSD0 : SD0 = S * D0)
    (hP0S : P0S = P0 * S)
    (hP02 : P02 = P0 * P0)
    (hS2 : S * S = 4 * (P0 * D0))
    (hX : X = 4 * P0 + 1045824536228 * S)
    (hY : Y = 546874480288255642233992 * D0)
    (hsub : Y + 3 <= X)
    (hE : E = X - (Y + 3)) :
  E * (E + 5) + 4 * P0 + 1143869499444786969588937946514124352 * SD0 + 1045824536228 * S + 6 =
    16 * P02 + 8366596289824 * P0S
    + 299071697190549708990652141928051192420480256064 * D02
    + 546874480288255642233992 * D0.
Proof.
  pose proof (sq_sub3_add2 (X - Y) ltac:(clear - hsub; lia)) as h1.
  replace ((X - Y) - 3) with E in h1 by (clear - hsub hE; lia).
  replace ((X - Y) + 2) with (E + 5) in h1 by (clear - hsub hE; lia).
  pose proof (sq_sub X Y ltac:(clear - hsub; lia)) as h2.
  assert (hXY : X * Y = 2187497921153022568935968 * (P0 * D0)
                        + 571934749722393484794468973257062176 * SD0).
  { rewrite hX, hY, N.mul_add_distr_r,
            (mul_coef 4 546874480288255642233992 P0 D0),
            (mul_coef 1045824536228 546874480288255642233992 S D0), <- hSD0.
    clear; lia. }
  assert (hXX : X * X = 16 * P02 + 8366596289824 * P0S
                        + 1093748960576511284467984 * (4 * (P0 * D0))).
  { rewrite hX, (sq_add (4 * P0) (1045824536228 * S)),
            (mul_coef 4 4 P0 P0), (mul_coef 4 1045824536228 P0 S),
            (mul_coef 1045824536228 1045824536228 S S),
            <- hP02, <- hP0S, hS2.
    clear; lia. }
  assert (hYY : Y * Y = 299071697190549708990652141928051192420480256064 * D02).
  { rewrite hY, (mul_coef 546874480288255642233992 546874480288255642233992 D0 D0), <- hD02.
    clear; lia. }
  rewrite hXY, hXX, hYY in h2.
  set (sqXY := (X - Y) * (X - Y)) in h1, h2; clearbody sqXY.
  set (EE5 := E * (E + 5)) in h1 |- *; clearbody EE5.
  set (P0D0 := P0 * D0) in h2; clearbody P0D0.
  clear - hX hY hsub hE h1 h2; lia.
Qed.

Lemma era10_step_core
    (a0 n D0 D02 S SD0 P0 P0S P02 k0 kz z E y Q r R QR KZR kv ma m_rem2 M11 A_next : N)
    (hD0 : 522912268115 <= D0)
    (hD02 : D0 <= D02)
    (hS : 522912268115 * D0 <= S)
    (hSD0 : 522912268115 * D02 <= SD0)
    (hSD0_S : S <= SD0)
    (hP0 : 571934749722393484794468973257062177 * SD0 <= P0)
    (hP0S : P0 <= P0S)
    (hP02 : 522912268115 * P0S <= P02)
    (hn : n = 2876311)
    (h2n : 2 ^ n = 2 * P02)
    (hA_def : a0 = 12 * (2 * P02) + 4183298144912 * P0S - 2)
    (hk0_def : k0 = 4 * P02 + 2091649072456 * P0S + 2876312)
    (hkz_def : kz = 4 * P02 - 2091649072456 * P0S - 2876315)
    (hz_def : z = 2 * kz)
    (hE_def : E = 4 * P0 + 1045824536228 * S - (546874480288255642233992 * D0 + 3))
    (hy_def : y = 2 * P0 + 571934749722393484794468973257062176 * SD0
      - 149535848595274854495326070964025596210240128032 * D02
      + 522912268114 * S - 273437240144127821116996 * D0 + 5752627)
    (hy_le_E : y + 1 <= E)
    (hy0_poly : E * (E + 5) + 4 * P0 + 1143869499444786969588937946514124352 * SD0
      + 1045824536228 * S + 6 =
      16 * P02 + 8366596289824 * P0S
      + 299071697190549708990652141928051192420480256064 * D02
      + 546874480288255642233992 * D0)
    (hQ_def : 2 ^ (y - 1) = Q)
    (hR_def : 2 ^ r = R)
    (hE_pow : 2 ^ E = 4 * QR)
    (hQ_ge : 16 * P02 <= Q)
    (_hR_ge : 2 * r + 6 <= R)
    (hQR_ge : 2 * Q <= QR)
    (hKZR_ge : 2 * kz - 1 <= KZR)
    (h6QR_ge : KZR <= 6 * QR)
    (hr_def : r = E - 1 - y)
    (hkv_def : kv = 6 * Q + kz - 3)
    (hma_def : ma = 24 * QR - 12 * Q - kz + y + 3)
    (hm_rem2_def : m_rem2 = 12 * QR - KZR + kz + E)
    (hkvR : (2 * kv + 5) * R = 12 * QR + KZR)
    (_hM11_def : M11 = 2 * P0 + 522912268114 * S - 273437240144127821116996 * D0)
    (hAnext_def : A_next = 12 * (4 * QR) + 4 * KZR - 2) :
  OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0).
Proof.
  assert (hkz_ge : 3 <= kz) by (clear - hD0 hS hSD0_S hP0 hP0S hP02 hkz_def; lia).
  assert (hkz_le_Q : kz <= Q) by (clear - hkz_def hQ_ge; lia).
  assert (hE_le_2kz : E + 4 <= 2 * kz) by (clear - hD0 hS hSD0_S hP0 hP0S hP02 hkz_def hE_def; lia).
  assert (hkv5 : 2 * kv + 5 = 12 * Q + (2 * kz - 1)) by (clear - hkz_ge hkv_def; lia).
  apply (era_mid_ge3_step a0 n k0 z E y ma kv r m_rem2 A_next).
  - rewrite h2n. clear - hD0 hS hSD0_S hP0 hP0S hP02 hn hA_def hk0_def; lia.
  - clear - hk0_def; lia.
  - rewrite h2n. clear - hD0 hS hSD0_S hP0 hP0S hP02 hk0_def hkz_def hz_def; lia.
  - clear - hy_le_E; lia.
  - set (EE5 := E * (E + 5)) in hy0_poly |- *; clearbody EE5.
    clear - hD0 hD02 hS hSD0 hSD0_S hP0 hk0_def hy_def hy0_poly; lia.
  - clear - hD0 hD02 hS hSD0 hSD0_S hP0 hy_def; lia.
  - clear - hy_le_E; lia.
  - rewrite hE_pow, hQ_def.
    clear - hkz_ge hkz_le_Q hy_le_E hQ_ge hQR_ge hkv_def hma_def; lia.
  - rewrite hQ_def. clear - hkz_ge hz_def hkv_def; lia.
  - rewrite hR_def.
    assert (h2kvR : 2 * (2 * kv + 5) * R = 2 * (12 * QR + KZR)) by (clear - hkvR; lia).
    rewrite h2kvR, hkv5.
    clear - hkz_ge hkz_le_Q hE_le_2kz hy_le_E hQ_ge hQR_ge hKZR_ge h6QR_ge hr_def hma_def hm_rem2_def; lia.
  - rewrite hR_def, hkvR.
    clear - hkz_ge hE_le_2kz hKZR_ge h6QR_ge hm_rem2_def; lia.
  - rewrite hR_def, hkvR.
    clear - hkz_ge hQ_ge hQR_ge hKZR_ge hAnext_def; lia.
Qed.

Lemma era10_full_core
    (p0_exp s_exp d_exp D0 D02 S SD0 P0 P0S P02 Q R QR k0 kz z E y r KZR kv ma m_rem2 M11 : N)
    (hp0 : p0_exp = 1438155) (hs : s_exp = 736251) (hd : d_exp = 34345)
    (hD0_def : D0 = 2 ^ d_exp)
    (hD02_def : D02 = D0 * D0)
    (hS_def : S = 2 ^ s_exp)
    (hSD0_def : SD0 = S * D0)
    (hP0_def : P0 = 2 ^ p0_exp)
    (hP0S_def : P0S = P0 * S)
    (hP02_def : P02 = P0 * P0)
    (hk0_def : k0 = 4 * P02 + 2091649072456 * P0S + 2876312)
    (hkz_def : kz = 4 * P02 - 2091649072456 * P0S - 2876315)
    (hz_def : z = 2 * kz)
    (hE_def : E = 4 * P0 + 1045824536228 * S - (546874480288255642233992 * D0 + 3))
    (hy_def : y = 2 * P0 + 571934749722393484794468973257062176 * SD0
      - 149535848595274854495326070964025596210240128032 * D02
      + 522912268114 * S - 273437240144127821116996 * D0 + 5752627)
    (hQ_def : Q = 2 ^ (y - 1))
    (hr_def : r = E - 1 - y)
    (hR_def : R = 2 ^ r)
    (hQR_def : QR = Q * R)
    (hKZR_def : KZR = (2 * kz - 1) * R)
    (hkv_def : kv = 6 * Q + kz - 3)
    (hma_def : ma = 24 * QR - 12 * Q - kz + y + 3)
    (hm_rem2_def : m_rem2 = 12 * QR - KZR + kz + E)
    (hM11_def : M11 = 2 * P0 + 522912268114 * S - 273437240144127821116996 * D0) :
  OrbitReachesPlus next (cfg_D1 (A10_gen p0_exp s_exp) 0 0) (cfg_SubTower M11 KZR)
  /\ SubTowerInv M11 KZR.
Proof.
  assert (h2_40 : 522912268115 <= 2 ^ 40) by N_decide.
  assert (h2_120 : 571934749722393484794468973257062177 <= 2 ^ 120) by N_decide.
  assert (hD0 : 522912268115 <= D0).
  { assert (h1 : 2 ^ 40 <= D0) by (rewrite hD0_def; apply pow2_mono; clear - hd; lia).
    clear - h2_40 h1; lia. }
  assert (hD02 : D0 <= D02) by (clear - hD0 hD02_def; nia).
  assert (hS : 522912268115 * D0 <= S).
  { assert (h1 : 2 ^ (40 + d_exp) <= S)
      by (rewrite hS_def; apply pow2_mono; clear - hs hd; lia).
    rewrite pow2_add, <- hD0_def in h1. clear - h1 h2_40; nia. }
  assert (hSD0 : 522912268115 * D02 <= SD0) by (clear - hSD0_def hD02_def hS; nia).
  assert (hSD0_S : S <= SD0) by (clear - hSD0_def hD0; nia).
  assert (hP0 : 571934749722393484794468973257062177 * SD0 <= P0).
  { assert (h1 : 2 ^ (120 + (s_exp + d_exp)) <= P0)
      by (rewrite hP0_def; apply pow2_mono; clear - hp0 hs hd; lia).
    rewrite !pow2_add, <- hS_def, <- hD0_def in h1.
    clear - h1 hSD0_def h2_120; nia. }
  assert (hP0S : P0 <= P0S) by (clear - hP0S_def hD0 hS; nia).
  assert (hP02 : 522912268115 * P0S <= P02) by (clear - hP02_def hP0S_def hP0 hSD0_S; nia).
  assert (hS2 : S * S = 4 * (P0 * D0)).
  { rewrite hS_def, hP0_def, hD0_def, <- !pow2_add.
    change 4 with (2 ^ 2); rewrite <- pow2_add.
    f_equal. clear - hp0 hs hd; lia. }
  assert (h2n : 2 ^ (p0_exp + p0_exp + 1) = 2 * P02).
  { rewrite !pow2_add, <- hP0_def; change (2 ^ 1) with 2.
    clear - hP02_def; nia. }
  assert (h2k2M : 2 * (522912268114 * 2 ^ s_exp) * 2 ^ (p0_exp + 2) = 4183298144912 * P0S).
  { rewrite pow2_add, <- hS_def, <- hP0_def; change (2 ^ 2) with 4.
    clear - hP0S_def; nia. }
  assert (hA_eq : A10_gen p0_exp s_exp = 12 * (2 * P02) + 4183298144912 * P0S - 2).
  { unfold A10_gen; rewrite h2n, h2k2M; reflexivity. }
  assert (hy_le_E : y + 1 <= E) by (clear - hD0 hD02 hS hSD0 hSD0_S hP0 hE_def hy_def; lia).
  assert (hy_pos : 2 <= y) by (clear - hD0 hD02 hS hSD0 hSD0_S hP0 hy_def; lia).
  assert (hE_pow : 2 ^ E = 4 * QR).
  { assert (hsub : E = (y - 1) + r + 2) by (clear - hy_le_E hy_pos hr_def; lia).
    rewrite hsub, !pow2_add, <- hQ_def, <- hR_def; change (2 ^ 2) with 4.
    clear - hQR_def; nia. }
  assert (hQ_ge : 16 * P02 <= Q).
  { assert (hy_exp : p0_exp + p0_exp + 4 <= y - 1)
      by (clear - hp0 hD0 hD02 hS hSD0 hSD0_S hP0 hy_def; lia).
    pose proof (pow2_mono hy_exp) as hmono.
    rewrite !pow2_add, <- hP0_def, <- hQ_def in hmono; change (2 ^ 4) with 16 in hmono.
    clear - hmono hP02_def; nia. }
  assert (hr_ge5 : 5 <= r)
    by (clear - hD0 hD02 hS hSD0 hSD0_S hP0 hE_def hy_def hr_def; lia).
  assert (hR_ge : 2 * r + 6 <= R).
  { rewrite hR_def; exact (pow2_ge_two_mul r hr_ge5). }
  assert (hQR_ge : 2 * Q <= QR) by (clear - hQR_def hR_ge; nia).
  assert (hkz_ge : 3 <= kz) by (clear - hD0 hS hSD0_S hP0 hP0S hP02 hkz_def; lia).
  assert (hkz_le_Q : kz <= Q) by (clear - hkz_def hQ_ge; lia).
  assert (hKZR_ge : 2 * kz - 1 <= KZR) by (clear - hKZR_def hR_ge; nia).
  assert (h6QR_ge : KZR <= 6 * QR)
    by (clear - hkz_le_Q hQR_def hKZR_def hkz_ge; nia).
  assert (hkv5 : 2 * kv + 5 = 12 * Q + (2 * kz - 1)) by (clear - hkz_ge hkv_def; lia).
  assert (hkvR : (2 * kv + 5) * R = 12 * QR + KZR)
    by (clear - hkv5 hQR_def hKZR_def; nia).
  assert (hAnext_eq : A_SubTower M11 KZR = 12 * (4 * QR) + 4 * KZR - 2).
  { unfold A_SubTower.
    replace (2 * M11 - 3) with E by (clear - hD0 hS hSD0_S hP0 hE_def hM11_def; lia).
    rewrite hE_pow; reflexivity. }
  pose proof (era10_hy0_poly P0 S D0 SD0 D02 P02 P0S
                (4 * P0 + 1045824536228 * S) (546874480288255642233992 * D0) E
                hD02_def hSD0_def hP0S_def hP02_def hS2 eq_refl eq_refl
                ltac:(clear - hD0 hS hSD0_S hP0; lia) hE_def) as hy0_poly.
  split.
  - unfold cfg_SubTower.
    exact (era10_step_core
             (A10_gen p0_exp s_exp) (p0_exp + p0_exp + 1)
             D0 D02 S SD0 P0 P0S P02 k0 kz z E y Q r R QR KZR kv ma m_rem2 M11
             (A_SubTower M11 KZR)
             hD0 hD02 hS hSD0 hSD0_S hP0 hP0S hP02
             ltac:(clear - hp0; lia) h2n hA_eq hk0_def hkz_def hz_def hE_def hy_def hy_le_E hy0_poly
             (eq_sym hQ_def) (eq_sym hR_def) hE_pow hQ_ge hR_ge hQR_ge hKZR_ge h6QR_ge
             hr_def hkv_def hma_def hm_rem2_def hkvR hM11_def hAnext_eq).
  - assert (hM11_ge : 128 <= M11) by (clear - hD0 hS hSD0_S hP0 hM11_def; lia).
    assert (hKZR_ge2 : 2 <= KZR) by (clear - hkz_ge hKZR_ge; lia).
    split; [exact hM11_ge | split; [exact hKZR_ge2 |]].
    assert (hpow_kz : 2 ^ (p0_exp + p0_exp + 3) = 8 * P02).
    { rewrite !pow2_add, <- hP0_def; change (2 ^ 3) with 8; clear - hP02_def; nia. }
    assert (hkz_le : 2 * kz - 1 <= 2 ^ (p0_exp + p0_exp + 3)).
    { rewrite hpow_kz; clear - hkz_def hkz_ge; lia. }
    assert (h4K11_le : 4 * KZR <= 2 ^ (M11 - 3)).
    { assert (h2 : 4 * KZR <= 2 ^ (2 + (p0_exp + p0_exp + 3) + r)).
      { do 2 rewrite pow2_add. rewrite <- hR_def; change (2 ^ 2) with 4.
        clear - hKZR_def hkz_le; nia. }
      assert (hexp : 2 + (p0_exp + p0_exp + 3) + r <= M11 - 3)
        by (clear - hp0 hD0 hD02 hS hSD0 hSD0_S hP0 hE_def hy_def hr_def hM11_def; lia).
      exact (N.le_trans _ _ _ h2 (pow2_mono hexp)). }
    assert (h4M11_le : 4 * M11 + 4 <= 2 ^ (M11 - 3)).
    { pose proof (pow2_ge_four_mul (M11 - 3) ltac:(clear - hM11_ge; lia)) as h1.
      clear - hM11_ge h1; lia. }
    assert (hpow_succ : 2 ^ (M11 - 2) = 2 ^ (M11 - 3) * 2).
    { replace (M11 - 2) with ((M11 - 3) + 1) by (clear - hM11_ge; lia).
      exact (pow2_succ (M11 - 3)). }
    clear - h4K11_le h4M11_le hpow_succ; lia.
Qed.

Lemma era10_gen (p0_exp s_exp d_exp : N)
    (hp0 : p0_exp = 1438155) (hs : s_exp = 736251) (hd : d_exp = 34345) :
  exists M11 K11,
    OrbitReachesPlus next (cfg_D1 (A10_gen p0_exp s_exp) 0 0) (cfg_SubTower M11 K11)
    /\ SubTowerInv M11 K11.
Proof.
  eexists _, _.
  eapply era10_full_core; [exact hp0 | exact hs | exact hd | reflexivity ..].
Qed.

Lemma sub_tower_step_core
    (M K P P2 n k0 kz z E y Q r R QR KZR kv ma m_rem2 M' K' a0 A_next : N)
    (hM : 128 <= M) (hK : 2 <= K) (hP_bound : 4 * K + 4 * M + 4 <= 2 ^ (M - 2))
    (hP_def : P = 2 ^ (M - 2))
    (hP2_def : P2 = P * P)
    (hn_def : n = 2 * M - 3)
    (hk0_def : k0 = 4 * P2 + 2 * K + 2 * M - 2)
    (hkz_def : kz = 4 * P2 - 2 * K - 2 * M - 1)
    (hz_def : z = 2 * kz)
    (hE_def : E = 4 * P - 3)
    (hy_def : y = 2 * P + 4 * K + 4 * M - 1)
    (hQ_def : Q = 2 ^ (y - 1))
    (hr_def : r = E - 1 - y)
    (hR_def : R = 2 ^ r)
    (hQR_def : QR = Q * R)
    (hKZR_def : KZR = (2 * kz - 1) * R)
    (hkv_def : kv = 6 * Q + kz - 3)
    (hma_def : ma = 24 * QR - 12 * Q - kz + y + 3)
    (hm_rem2_def : m_rem2 = 12 * QR - KZR + kz + E)
    (hM'_def : M' = 2 * P)
    (hK'_def : K' = KZR)
    (hA_def : a0 = A_SubTower M K)
    (hAnext_def : A_next = A_SubTower M' K') :
  OrbitReachesPlus next (cfg_D1 a0 0 0) (cfg_D1 A_next 0 0) /\ SubTowerInv M' K'.
Proof.
  assert (hP_ge : 4 * K + 4 * M + 4 <= P) by (rewrite hP_def; exact hP_bound).
  assert (hP2_ge_16P : 16 * P <= P2) by (clear - hM hK hP_ge hP2_def; nia).
  assert (h2M3 : 2 ^ (2 * M - 3) = 2 * P2).
  { assert (hsub : 2 * M - 3 = (M - 2) + (M - 2) + 1) by (clear - hM; lia).
    rewrite hsub, !pow2_add, <- hP_def; change (2 ^ 1) with 2.
    clear - hP2_def; nia. }
  assert (hy_le_E : y + 1 <= E) by (clear - hM hK hP_ge hE_def hy_def; lia).
  assert (hy_pos : 2 <= y) by (clear - hM hK hP_ge hy_def; lia).
  assert (hQR : 2 ^ E = 4 * QR).
  { assert (hsub : E = (y - 1) + r + 2) by (clear - hy_le_E hy_pos hr_def; lia).
    rewrite hsub, !pow2_add, <- hQ_def, <- hR_def; change (2 ^ 2) with 4.
    clear - hQR_def; nia. }
  assert (hQ_ge_16P2 : 16 * P2 <= Q).
  { assert (hy_exp : (M - 2) + (M - 2) + 4 <= y - 1)
      by (clear - hM hK hP_ge hy_def; lia).
    pose proof (pow2_mono hy_exp) as hmono.
    rewrite !pow2_add, <- hP_def, <- hQ_def in hmono; change (2 ^ 4) with 16 in hmono.
    clear - hmono hP2_def; nia. }
  assert (hr_ge5 : 5 <= r) by (clear - hM hK hP_ge hE_def hy_def hr_def; lia).
  assert (hR_ge : 2 * r + 6 <= R) by (rewrite hR_def; exact (pow2_ge_two_mul r hr_ge5)).
  assert (hQR_ge_2Q : 2 * Q <= QR) by (clear - hQR_def hR_ge; nia).
  assert (hkz_ge : 3 <= kz) by (clear - hM hK hP_ge hP2_ge_16P hkz_def; lia).
  assert (hkz_le_Q : kz <= Q) by (clear - hkz_def hQ_ge_16P2; lia).
  assert (hE_le_2kz : E + 4 <= 2 * kz) by (clear - hM hK hP_ge hP2_ge_16P hkz_def hE_def; lia).
  assert (hKZR_ge : 2 * kz - 1 <= KZR) by (clear - hKZR_def hR_ge; nia).
  assert (h6QR_ge_KZR : KZR <= 6 * QR)
    by (clear - hkz_le_Q hkz_ge hQR_def hKZR_def; nia).
  assert (hkv5 : 2 * kv + 5 = 12 * Q + (2 * kz - 1)) by (clear - hkz_ge hkv_def; lia).
  assert (hkvR : (2 * kv + 5) * R = 12 * QR + KZR)
    by (clear - hkv5 hQR_def hKZR_def; nia).
  split.
  - apply (era_mid_ge3_step a0 n k0 z E y ma kv r m_rem2 A_next).
    + rewrite hA_def; unfold A_SubTower.
      rewrite hn_def, h2M3.
      clear - hM hK hP_ge hP2_ge_16P hk0_def; lia.
    + clear - hM hK hk0_def; lia.
    + rewrite hn_def, h2M3.
      clear - hM hK hP_ge hP2_ge_16P hk0_def hkz_def hz_def; lia.
    + clear - hy_le_E; lia.
    + pose proof (sq_sub3_add2 (4 * P) ltac:(clear - hM hK hP_ge; lia)) as hA_sq.
      replace (4 * P - 3) with E in hA_sq by exact hE_def.
      replace (4 * P + 2) with (E + 5) in hA_sq by (clear - hM hK hP_ge hE_def; lia).
      rewrite (mul_coef 4 4 P P), <- hP2_def in hA_sq.
      set (EE5 := E * (E + 5)) in hA_sq |- *; clearbody EE5.
      clear - hM hK hP_ge hk0_def hy_def hA_sq; lia.
    + exact hy_pos.
    + clear - hy_le_E; lia.
    + rewrite hQR, <- hQ_def.
      clear - hkz_ge hkz_le_Q hy_pos hQ_ge_16P2 hQR_ge_2Q hkv_def hma_def; lia.
    + rewrite <- hQ_def. clear - hkz_ge hz_def hkv_def; lia.
    + rewrite <- hR_def.
      assert (h2kvR : 2 * (2 * kv + 5) * R = 2 * (12 * QR + KZR)) by (clear - hkvR; lia).
      rewrite h2kvR, hkv5.
      clear - hkz_ge hkz_le_Q hE_le_2kz hy_le_E hQ_ge_16P2 hQR_ge_2Q hKZR_ge h6QR_ge_KZR hr_def hma_def hm_rem2_def; lia.
    + rewrite <- hR_def, hkvR.
      clear - hkz_ge hE_le_2kz hKZR_ge h6QR_ge_KZR hm_rem2_def; lia.
    + rewrite hAnext_def; unfold A_SubTower.
      rewrite <- hR_def, hkvR, hK'_def.
      replace (4 * (12 * QR + KZR - 4) + 14) with (12 * (4 * QR) + 4 * KZR - 2)
        by (clear - hkz_ge hKZR_ge; lia).
      rewrite <- hQR.
      replace E with (2 * M' - 3) by (clear - hM hK hP_ge hE_def hM'_def; lia).
      reflexivity.
  - assert (hM'_ge : 128 <= M') by (clear - hM hK hP_ge hM'_def; lia).
    assert (hK'_ge : 2 <= K') by (clear - hkz_ge hKZR_ge hK'_def; lia).
    split; [exact hM'_ge | split; [exact hK'_ge |]].
    assert (hkz_le : 2 * kz - 1 <= 2 ^ (2 * M - 1)).
    { assert (hsub : 2 * M - 1 = (M - 2) + (M - 2) + 3) by (clear - hM; lia).
      rewrite hsub, !pow2_add, <- hP_def; change (2 ^ 3) with 8.
      assert (h8P2 : (P * P) * 8 = 8 * P2) by (clear - hP2_def; nia).
      rewrite h8P2. clear - hkz_def hkz_ge; lia. }
    assert (h4K'_le : 4 * K' <= 2 ^ (M' - 3)).
    { assert (h2 : 4 * K' <= 2 ^ (2 + (2 * M - 1) + r)).
      { do 2 rewrite pow2_add. rewrite <- hR_def; change (2 ^ 2) with 4.
        clear - hK'_def hKZR_def hkz_le; nia. }
      assert (hexp : 2 + (2 * M - 1) + r <= M' - 3)
        by (clear - hM hK hP_ge hE_def hy_def hr_def hM'_def; lia).
      exact (N.le_trans _ _ _ h2 (pow2_mono hexp)). }
    assert (h4M'_le : 4 * M' + 4 <= 2 ^ (M' - 3)).
    { pose proof (pow2_ge_four_mul (M' - 3) ltac:(clear - hM'_ge; lia)) as h1.
      clear - hM'_ge h1; lia. }
    assert (hpow_succ : 2 ^ (M' - 2) = 2 ^ (M' - 3) * 2).
    { replace (M' - 2) with ((M' - 3) + 1) by (clear - hM'_ge; lia).
      exact (pow2_succ (M' - 3)). }
    clear - h4K'_le h4M'_le hpow_succ; lia.
Qed.

Lemma sub_tower_step (M K : N) (hinv : SubTowerInv M K) :
  exists M' K',
    OrbitReachesPlus next (cfg_SubTower M K) (cfg_SubTower M' K') /\ SubTowerInv M' K'.
Proof.
  destruct hinv as [hM [hK hP_bound]].
  unfold cfg_SubTower.
  eexists _, _.
  eapply sub_tower_step_core;
    [exact hM | exact hK | exact hP_bound | reflexivity ..].
Qed.

Lemma start_reaches_sub_tower :
  exists M11 K11,
    OrbitReachesPlus next start (cfg_SubTower M11 K11) /\ SubTowerInv M11 K11.
Proof.
  pose proof (orp_trans era1 era2) as h12.
  pose proof (orp_trans h12 era3) as h3.
  pose proof (orp_trans h3 era4) as h4.
  pose proof (orp_trans h4 era5) as h5.
  pose proof (orp_trans h5 era6) as h6.
  pose proof (orp_trans h6 era7) as h7.
  pose proof (orp_trans h7 era8) as h8.
  pose proof (era9_gen 1438155 736251 701901 eq_refl eq_refl eq_refl) as h9.
  pose proof (orp_trans h8 h9) as h89.
  destruct (era10_gen 1438155 736251 34345 eq_refl eq_refl eq_refl) as [M11 [K11 [h10 hinv11]]].
  exists M11, K11.
  exact (conj (orp_trans h89 h10) hinv11).
Qed.

Definition InSubTowerSystem (cfg : Q * tape) : Prop :=
  exists M K : N, cfg = encode (cfg_SubTower M K) /\ SubTowerInv M K.

Lemma nonhalt : ~ halts tm c0.
Proof.
  destruct start_reaches_sub_tower as [M11 [K11 [hreach hinv]]].
  eapply multistep_nonhalt.
  - exact (pev (ptrans init_reaches_start (orbitPlus_sound hreach))).
  - eapply (progress_nonhalt tm InSubTowerSystem).
    + intros cfg [M [K [-> hMK]]].
      destruct (sub_tower_step M K hMK) as [M' [K' [hstep hMK']]].
      exists (encode (cfg_SubTower M' K')).
      split.
      * exists M', K'. exact (conj eq_refl hMK').
      * exact (orbitPlus_sound hstep).
    + exists M11, K11. exact (conj eq_refl hinv).
Qed.
