From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Ltac tape_eq :=
  simpl_tape; cbn;
  repeat rewrite lpow_mul;
  simpl_rotate;
  reflexivity.

Lemma Sn_le_pow2n n:
  n+1 <= 2^n.
Proof.
  induction n; cbn; lia.
Qed.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC1RB_0RD0RC_1LD1LE_0LF0LE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{F}} [0] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1;1]^^m *> [0]^^(n*2) *> r -->*
  l <{{A}} [1;0]^^(n+1) *> [1;1]^^(n*2+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1;1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1;1]^^(n+1) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1;1]^^0 *> [0]^^(n') *> [1]^^(4+m*2+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n*2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1;1]^^(1+n) <* [0]^^(n4+1) <| [1;1]^^(2+m+n2) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    replace n4 with (n2*2) by lia.
    tape_eq.
  }
  follow HP1.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+2*n) by lia.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{A}} [1;0]^^(2^i*2-1+1) *> [1;1]^^((2^i*2-1)*2+2) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RB_0RD0RC_1LD1LE_0LF0LE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{F}} [0] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1;1]^^m *> [0]^^(n*2) *> r -->*
  l <{{A}} [1;1]^^n *> [1;0] *> [1;1]^^(n*2+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1;1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1;1]^^(n+1) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1;1]^^0 *> [0]^^(n') *> [1]^^(4+m*2+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n*2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1;1]^^(1+n) <* [0]^^(n4+1) <| [1;1]^^(2+m+n2) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    replace n4 with (n2*2) by lia.
    tape_eq.
  }
  follow HP1.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+2*n) by lia.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{A}} [1;1]^^(2^i*2-1) *> [1;0] *> [1;1]^^((2^i*2-1)*2+2) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC0RB_1LC1LD_1LE0LD_0LF---_1RA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{E}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{F}} [1]^^(n*2) *> [0;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{F}} [1]^^((2^i*2-1)*2) *> [0;1] *> [1]^^((2^i*2-1)*4+3) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC---_1RD0LC_1RD1RE_0RF0RE_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{F}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{B}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{C}} [0]^^(n*2) *> [1;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{C}} [0]^^((2^i*2-1)*2) *> [1;1] *> [1]^^((2^i*2-1)*4+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM4.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC---_1RD0LC_1RC1RE_0RF0RE_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{F}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{B}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{C}} [0]^^(n*2) *> [1;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{C}} [0]^^((2^i*2-1)*2) *> [1;1] *> [1]^^((2^i*2-1)*4+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM5.


Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC---_1RD1LC_1RE1RD_0RF0RE_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{F}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{B}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{C}} [1]^^(n*2) *> [0;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{C}} [1]^^((2^i*2-1)*2) *> [0;1] *> [1]^^((2^i*2-1)*4+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM6.


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC---_1RD0LC_1RD0RE_0RF0RE_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{F}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{B}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{C}} [0]^^(n*2) *> [0;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{C}} [0]^^((2^i*2-1)*2) *> [0;1] *> [1]^^((2^i*2-1)*4+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB0LA_0LC---_1RD0LC_1RD0RE_0RF0RD_1LF1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{F}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{B}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1;1]^^m *> [0]^^(n*2) *> r -->*
  l <{{C}} [0;0]^^n *> [0;1] *> [1;1]^^(n*2+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1;1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1;1]^^(n+1) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1;1]^^0 *> [0]^^(n') *> [1]^^(4+m*2+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n*2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1;1]^^(1+n) <* [0]^^(n4+1) <| [1;1]^^(2+m+n2) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    replace n4 with (n2*2) by lia.
    tape_eq.
  }
  follow HP1.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+2*n) by lia.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{C}} [0;0]^^(2^i*2-1) *> [0;1] *> [1;1]^^((2^i*2-1)*2+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM8.


Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LD_0RD1RC_0RE0RD_1LE1LF_0LA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{E}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [0] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1;1]^^m *> [0]^^(n*2) *> r -->*
  l <{{B}} [1;0]^^(n+1) *> [1;1]^^(n*2+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1;1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1;1]^^(n+1) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1;1]^^0 *> [0]^^(n') *> [1]^^(4+m*2+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n*2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1;1]^^(1+n) <* [0]^^(n4+1) <| [1;1]^^(2+m+n2) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    replace n4 with (n2*2) by lia.
    tape_eq.
  }
  follow HP1.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+2*n) by lia.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{B}} [1;0]^^(2^i*2-1+1) *> [1;1]^^((2^i*2-1)*2+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_0RD1RC_0RE0RD_1LE1LF_0LA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{E}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [0] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{B}} [1]^^(n*2) *> [1;0] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1_all' i:
  c0 -->*
  const 0 <{{B}} [1]^^((2^i*2-1)*2) *> [1;0] *> [1]^^((2^i*2-1)*4+0) *> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{F}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{A}} [1]^^(n*2) *> [0;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Definition cfg n m :=
  const 0 <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> const 0.

Lemma BigStep n0 m:
  P1 (n0+1) ->
  cfg (n0+1) m -->* cfg ((n0+1)*2+1) m.
Proof.
  intros HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  remember (n0+1) as n.
  unfold cfg.
  mid (const 0 <* [0]^^(n*4+3) <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> [0]^^(n*2+1) *> const 0).
  1:{
    finish.
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    reflexivity.
  }
  unfold P1 in HP1.
  unfold P1' in HP1'.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  remember (const 0) as e0.
  mid (e0 <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(3+m+n4) *> [0]^^n2 *> e0).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (e0 <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((3+m+n4)) *> [0]^^n2 *> e0).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  subst e0.
  replace (n'*4+m) with (4+n4+m+n4) by lia.
  replace (n'*2+2) with (4+n2+n2) by lia.
  es.
Qed.

Lemma cfg_all i:
  c0 -->*
  cfg (2^i*2-1) 0.
Proof.
  induction i.
  - cbn.
    unfold cfg.
    es.
  - follow IHi.
    pose proof (Nat.pow_nonzero 2 i).
    applys_eq (BigStep (2^i*2-2)).
    1,2: f_equal; cbn; lia.
    applys_eq (P1_all i).
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (cfg_all n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LB_1RC1RD_0RE0RD_1LE1LF_1LA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{E}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{B}} [0]^^(n*2) *> [1;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Definition cfg n m :=
  const 0 <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> const 0.

Lemma BigStep n0 m:
  P1 (n0+1) ->
  cfg (n0+1) m -->* cfg ((n0+1)*2+1) m.
Proof.
  intros HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  remember (n0+1) as n.
  unfold cfg.
  mid (const 0 <* [0]^^(n*4+3) <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> [0]^^(n*2+1) *> const 0).
  1:{
    finish.
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    reflexivity.
  }
  unfold P1 in HP1.
  unfold P1' in HP1'.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  remember (const 0) as e0.
  mid (e0 <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(3+m+n4) *> [0]^^n2 *> e0).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (e0 <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((3+m+n4)) *> [0]^^n2 *> e0).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  subst e0.
  replace (n'*4+m) with (4+n4+m+n4) by lia.
  replace (n'*2+2) with (4+n2+n2) by lia.
  es.
Qed.

Lemma cfg_all i:
  c0 -->*
  cfg (2^i*2-1) 0.
Proof.
  induction i.
  - cbn.
    unfold cfg.
    es.
  - follow IHi.
    pose proof (Nat.pow_nonzero 2 i).
    applys_eq (BigStep (2^i*2-2)).
    1,2: f_equal; cbn; lia.
    applys_eq (P1_all i).
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (cfg_all n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LB_1RB1RD_0RE0RD_1LE1LF_1LA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{E}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1] *> r) (at level 30).

Definition P1 n :=
  forall m l r,
  l <* [0]^^(n*4+1) <| [1]^^(m) *> [0]^^(n*2) *> r -->*
  l <{{B}} [0]^^(n*2) *> [1;1] *> [1]^^(n*4+m) *> r.

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [1]^^(m) *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*4+m+1) |> r.

Lemma P1_P1' n0:
  P1 (n0+1) ->
  P1' (n0+1).
Proof.
  unfold P1,P1'.
  intros HP1.
  intros.
  specialize (HP1 m ([0] *> l) ([0] *> r)).
  remember (n0+1) as n.
  replace (n*4+2) with (n*4+1+1) by lia.
  remember (n*4+1) as v1.
  rewrite (Nat.add_comm (n*4)).
  repeat rewrite lpow_add.
  repeat rewrite Str_app_assoc.
  follow HP1.
  subst n.
  replace ((n0+1)*2) with (2+n0*2) by lia.
  replace ((n0+1)*4) with (4+n0*4) by lia.
  es.
Qed.

Lemma P1_S n0:
  P1 (n0+1) ->
  P1 ((n0+1)*2+1).
Proof.
  unfold P1.
  intro HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  unfold P1' in HP1'.
  intros.
  remember (n0+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*4+1) with (n4+2+(n4+3)) by lia.
  replace (n'*2) with (n'+n') by lia.
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ (n')).
  repeat rewrite Str_app_assoc.
  replace (n'+n') with (n'*2) by lia.
  follow HP1'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  mid (l <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(4+m+n4) *> [0]^^n2 *> r).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((4+m+n4)) *> [0]^^n2 *> r).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  replace (n4+(4+m+n4)) with (n'*4+m) by lia.
  replace (n'*2) with (2*n') by lia.
  subst n'.
  es.
Qed.

Lemma P1_all i:
  P1 (2^i*2-1).
Proof.
  induction i.
  - unfold P1; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1_S (2^i*2-2)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Definition cfg n m :=
  const 0 <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> const 0.

Lemma BigStep n0 m:
  P1 (n0+1) ->
  cfg (n0+1) m -->* cfg ((n0+1)*2+1) m.
Proof.
  intros HP1.
  pose proof (P1_P1' _ HP1) as HP1'.
  remember (n0+1) as n.
  unfold cfg.
  mid (const 0 <* [0]^^(n*4+3) <* [1]^^(n*2+2) <* [0]^^(n*4+m) |> [0]^^(n*2+1) *> const 0).
  1:{
    finish.
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    rewrite (lpow_all0 [0]); [|solve_const0_eq].
    reflexivity.
  }
  unfold P1 in HP1.
  unfold P1' in HP1'.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^n') with ([0]^^(1+n2)) by (f_equal; lia).
  remember (const 0) as e0.
  mid (e0 <* [0]^^(n4+2) <| [1]^^(0*2) *> [0]^^(n') *> [1]^^(3+m+n4) *> [0]^^n2 *> e0).
  1:{
    do 3 (er; sr).
    step1.
    finish.
    replace n' with (1+n2) by lia.
    tape_eq.
  }
  follow HP1'.
  mid (e0 <* [1]^^(2+n2) <* [0]^^(n4+1) <| [1]^^((3+m+n4)) *> [0]^^n2 *> e0).
  1:{
    step1.
    step1.
    finish.
    tape_eq.
  }
  follow HP1.
  subst e0.
  replace (n'*4+m) with (4+n4+m+n4) by lia.
  replace (n'*2+2) with (4+n2+n2) by lia.
  replace n2 with (n*2) by lia.
  es.
Qed.

Lemma cfg_all i:
  c0 -->*
  cfg (2^i*2-1) 0.
Proof.
  induction i.
  - cbn.
    unfold cfg.
    es.
  - follow IHi.
    pose proof (Nat.pow_nonzero 2 i).
    applys_eq (BigStep (2^i*2-2)).
    1,2: f_equal; cbn; lia.
    applys_eq (P1_all i).
    lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (cfg_all n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM13.


Lemma merge_lpow {A} (a:list A) n1 n2 b:
  a^^n1 *> a^^n2 *> b =
  a^^(n1+n2) *> b.
Proof.
  simpl_tape.
  reflexivity.
Qed.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_1RE---_1RE0RF_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1;1] *> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*6+3) <| [1]^^m *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*6+m+2) |> r.

Lemma P1'_S n:
  P1' (n) ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*6) as n6.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace (n'*6+3) with (n6+3+(n6+6)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n6+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^2 <* [0]^^(n6+3) <| [1]^^0 *> [0]^^(n4+1) *> [1]^^(5+m+n6) *> [0]^^(n4+3) *> r).
  1:{
    subst n4 n6.
    simpl_tape.
    er. sr.
    er. sr.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^2 <* [1]^^(n4+3) <* [0]^^(n6+3) <| [1]^^(3+m+n6) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    step1.
    finish.
    subst n4 n6.
    tape_eq.
  }
  follow HP1'.
  replace (n'*6+m+2) with (8+n6+m+n6) by lia.
  replace (n'*4+3) with (7+n4*2) by lia.
  er. sr.
  er. sr.
  rewrite merge_lpow.
  replace (n4+n4) with (n4*2) by lia. 
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1'_S (2^i-1)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*6+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM14.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_1RE---_1RD0RF_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1;1] *> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*6+3) <| [1]^^m *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*6+m+2) |> r.

Lemma P1'_S n:
  P1' (n) ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*6) as n6.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace (n'*6+3) with (n6+3+(n6+6)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n6+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^2 <* [0]^^(n6+3) <| [1]^^0 *> [0]^^(n4+1) *> [1]^^(5+m+n6) *> [0]^^(n4+3) *> r).
  1:{
    subst n4 n6.
    simpl_tape.
    er. sr.
    er. sr.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^2 <* [1]^^(n4+3) <* [0]^^(n6+3) <| [1]^^(3+m+n6) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    step1.
    finish.
    subst n4 n6.
    tape_eq.
  }
  follow HP1'.
  replace (n'*6+m+2) with (8+n6+m+n6) by lia.
  replace (n'*4+3) with (7+n4*2) by lia.
  er. sr.
  er. sr.
  rewrite merge_lpow.
  replace (n4+n4) with (n4*2) by lia. 
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1'_S (2^i-1)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*6+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM15.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_1RD0RE_---0RF_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1;1] *> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*6+3) <| [1]^^m *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*6+m+2) |> r.

Lemma P1'_S n:
  P1' (n) ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*6) as n6.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace (n'*6+3) with (n6+3+(n6+6)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n6+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^2 <* [0]^^(n6+3) <| [1]^^0 *> [0]^^(n4+1) *> [1]^^(5+m+n6) *> [0]^^(n4+3) *> r).
  1:{
    subst n4 n6.
    simpl_tape.
    er. sr.
    er. sr.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^2 <* [1]^^(n4+3) <* [0]^^(n6+3) <| [1]^^(3+m+n6) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    step1.
    finish.
    subst n4 n6.
    tape_eq.
  }
  follow HP1'.
  replace (n'*6+m+2) with (8+n6+m+n6) by lia.
  replace (n'*4+3) with (7+n4*2) by lia.
  er. sr.
  er. sr.
  rewrite merge_lpow.
  replace (n4+n4) with (n4*2) by lia. 
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1'_S (2^i-1)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*6+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM16.


Module TM17.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_1RD0RE_---0RF_0RB0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1;1] *> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*6+3) <| [1]^^(m*3) *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*6+m*3+2) |> r.

Lemma P1'_S n:
  P1' (n) ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*6) as n6.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace (n'*6+3) with (n6+3+(n6+6)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n6+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^2 <* [0]^^(n6+3) <| [1]^^(0*3) *> [0]^^(n4+1) *> [1]^^(5+m*3+n6) *> [0]^^(n4+3) *> r).
  1:{
    subst n4 n6.
    simpl_tape.
    er. sr.
    er. sr.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^2 <* [1]^^(n4+3) <* [0]^^(n6+3) <| [1]^^(3+m*3+n6) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    step1.
    finish.
    subst n4 n6.
    tape_eq.
  }
  replace (3+m*3+n6) with ((1+m+n*2)*3) by lia.
  follow HP1'.
  replace (n'*6+m*3+2) with (8+n6+n6+m*3) by lia.
  replace (n'*4+3) with (7+n4*2) by lia.
  er. sr.
  er. sr.
  rewrite merge_lpow.
  replace (n4+n4) with (n4*2) by lia. 
  subst n4 n6.
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1'_S (2^i-1)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*6+0*3+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM17.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_1RD1RE_---1LF_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Notation "l <| r" :=
    (l <{{A}} [1;1] *> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*6+3) <| [1]^^(m*3) *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*6+m*3+2) |> r.

Lemma P1'_S n:
  P1' (n) ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*6) as n6.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace (n'*6+3) with (n6+3+(n6+6)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n6+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^2 <* [0]^^(n6+3) <| [1]^^(0*3) *> [0]^^(n4+1) *> [1]^^(5+m*3+n6) *> [0]^^(n4+3) *> r).
  1:{
    subst n4 n6.
    simpl_tape.
    er. sr.
    er. sr.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^2 <* [1]^^(n4+3) <* [0]^^(n6+3) <| [1]^^(3+m*3+n6) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    step1.
    finish.
    subst n4 n6.
    tape_eq.
  }
  replace (3+m*3+n6) with ((1+m+n*2)*3) by lia.
  follow HP1'.
  replace (n'*6+m*3+2) with (8+n6+n6+m*3) by lia.
  replace (n'*4+3) with (7+n4*2) by lia.
  er. sr.
  er. sr.
  rewrite merge_lpow.
  replace (n4+n4) with (n4*2) by lia. 
  subst n4 n6.
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i).
    applys_eq (P1'_S (2^i-1)).
    2: applys_eq IHi; lia.
    cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*6+0*3+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC---_0RD0RC_1LD0LE_1RB0LF_1RB0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  do 3 step1.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  do 3 step1.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+3+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM19.


Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB1LD_0RC0RB_1LC1RA_---0LE_1RA0LF_1RA0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 5 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 5 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+2+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM20.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC0RB_1LC0LD_1RA0LE_1RA1LF_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+2+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM21.


Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC0RB_1LC0LD_1RA0LE_1RA0LF_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+2+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM22.


Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC1LE_0RD0RC_1LD1RB_---0LA_1RB0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 5 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 5 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+0+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM23.


Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC---_0RD0RC_1LD0LE_1RB0LA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+0+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM24.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC0LD_0RD0RC_1LD0LA_1RB1LF_---1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{D}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) |> [1]^^m *> [0]^^(n*4+3) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*2+m+1) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  replace (n'*4+3) with (n4+3+(n4+4)) by lia.
  rewrite (lpow_add _ n' (n'+1)).
  rewrite (lpow_add _ (n4+3)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^n' |> [1]^^0 *> [0]^^(n4+3) *> [1]^^(3+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    subst n4.
    replace (n*4) with (4+n0*4*3) by lia.
    rewrite lpow_add.
    rewrite lpow_mul.
    er. sr.
    step1.
    step1.
    subst n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^n' |> [1]^^(2+m+n2) *> [0]^^(n4+3) *> r).
  1:{
    do 3 step1.
    finish.
    subst n4 n2 n'.
    tape_eq.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n4 n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*2+0+1) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM25.


Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RC0RD_1LA0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{D}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM26.


Module TM27.
Definition tm := Eval compute in (TM_from_str "1LB0LF_0RC0RB_1LC1LD_1RE0LA_0LC1RB_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM27.


Module TM28.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RC0RD_1RB0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{D}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(3+m+n2) *> [0]^^(n') *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    do 3 step1.
    finish.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM28.


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RD_0LB1LA_0RB1LE_1RB0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{E}} [0;1;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{D}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [0;1]^^m *> [0]^^(n*4) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace ([0]^^(n'*4+2)) with ([0]^^(n4+2+(n4+4))) by (f_equal; lia).
  replace ([0]^^(n'*4)) with ([0]^^(n4+(n4+4))) by (f_equal; lia).
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ n4 (n4+4)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^(n4+2) <| [0;1]^^1 *> [0]^^n4 *> [1] *> [1;0]^^(2+m+n*2) *> [0]^^(n4+1) *> r).
  1:{
    replace (n4+4) with (4+n4) by lia.
    replace (n4+m*2+1) with (1+(n*2+m)*2) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    er. sr.
    er.
    replace n4 with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 14 step1.
    subst n' n4 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^(n4+2) <| [0;1]^^(2+m+n*2) *> [0]^^(n4) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    step1.
    step1.
    finish.
  }
  follow HP1'.
  replace (n4+(2+m+n*2)*2) with (n'*4+m*2) by lia.
  replace (n'*4) with (4+n4+n4) by lia.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace ([0]^^(n'*4+2)) with ([0]^^(n4+2+(n4+4))) by (f_equal; lia).
  replace ([0]^^(n'*4)) with ([0]^^(n4+(n4+4))) by (f_equal; lia).
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ n4 (n4+4)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^(n4+2) <| [0;1]^^1 *> [0]^^n4 *> [1] *> [1;0]^^(2+m+n*2) *> [0]^^(n4+1) *> r).
  1:{
    replace (n4+4) with (4+n4) by lia.
    replace (n4+m*2+1) with (1+(n*2+m)*2) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    er. sr.
    er.
    replace n4 with (4+n0*4*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 14 step1.
    subst n' n4 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^(n4+2) <| [0;1]^^(2+m+n*2) *> [0]^^(n4) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    step1.
    step1.
    finish.
  }
  follow HP1'.
  replace (n4+(2+m+n*2)*2) with (n'*4+m*2) by lia.
  replace (n'*4) with (4+n4+n4) by lia.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*4+1*2+1) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM29.


Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0RE_0LB1LD_1RB0LA_0RB1LD_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{E}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*4+2) <| [0;1]^^m *> [0]^^(n*4) *> r -->*
  l <* [1]^^(n*4+4) <* [0]^^(n*4+m*2+1) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace ([0]^^(n'*4+2)) with ([0]^^(n4+2+(n4+4))) by (f_equal; lia).
  replace ([0]^^(n'*4)) with ([0]^^(n4+(n4+4))) by (f_equal; lia).
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ n4 (n4+4)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^(n4+2) <| [0;1]^^1 *> [0]^^n4 *> [1] *> [1;0]^^(2+m+n*2) *> [0]^^(n4+1) *> r).
  1:{
    replace (n4+4) with (4+n4) by lia.
    replace (n4+m*2+1) with (1+(n*2+m)*2) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    er. sr.
    er.
    replace n4 with (n0*4*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 14 step1.
    subst n' n4 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^(n4+2) <| [0;1]^^(2+m+n*2) *> [0]^^(n4) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    step1.
    step1.
    finish.
  }
  follow HP1'.
  replace (n4+(2+m+n*2)*2) with (n'*4+m*2) by lia.
  replace (n'*4) with (4+n4+n4) by lia.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*4) as n4.
  remember (n*2+1) as n'.
  replace ([0]^^(n'*4+2)) with ([0]^^(n4+2+(n4+4))) by (f_equal; lia).
  replace ([0]^^(n'*4)) with ([0]^^(n4+(n4+4))) by (f_equal; lia).
  rewrite (lpow_add _ (n4+2)).
  rewrite (lpow_add _ n4 (n4+4)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  mid (l <* [0]^^(n4+2) <| [0;1]^^1 *> [0]^^n4 *> [1] *> [1;0]^^(2+m+n*2) *> [0]^^(n4+1) *> r).
  1:{
    replace (n4+4) with (4+n4) by lia.
    replace (n4+m*2+1) with (1+(n*2+m)*2) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    er. sr.
    er.
    replace n4 with (4+n0*4*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 14 step1.
    subst n' n4 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n4+4) <* [0]^^(n4+2) <| [0;1]^^(2+m+n*2) *> [0]^^(n4) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    step1.
    step1.
    finish.
  }
  follow HP1'.
  replace (n4+(2+m+n*2)*2) with (n'*4+m*2) by lia.
  replace (n'*4) with (4+n4+n4) by lia.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+4) <* [0]^^((2^i-1)*4+1*2+1) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM30.


Module TM31.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1LC0LE_1RD0LF_0RE0RD_1RA1LB_0LC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{C}} [1;1;0] *> r) (at level 30).

Notation "l |0> r" :=
    (l {{D}}> r) (at level 30).

Notation "l |1> r" :=
    (l {{E}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [0] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |0> r.

Definition P1 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [1] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |1> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+6) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(8+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P0 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+4) *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(6+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) /\
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3).
Proof.
  induction i.
  - unfold P0,P1.
    split; es.
  - destruct IHi as [HP0 HP1].
    remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ HP0 HP1) as HP0'.
    pose proof (P1_S _ HP0 HP1) as HP1'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    split.
    + applys_eq (P0_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
    + applys_eq (P1_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
Qed.

Lemma P1'_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(2+(n*2+3)+2) |0> const 0.
Proof.
  pose proof (P_all i) as [HP0 HP1].
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  cbn[Str_app].
  rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM31.


Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB0LD_1RC0LF_0RD0RC_1RE1LA_1LA0LA_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{B}} [1;1;0] *> r) (at level 30).

Notation "l |0> r" :=
    (l {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l {{D}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [0] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |0> r.

Definition P1 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [1] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |1> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+6) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(8+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P0 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+4) *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(6+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) /\
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3).
Proof.
  induction i.
  - unfold P0,P1.
    split; es.
  - destruct IHi as [HP0 HP1].
    remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ HP0 HP1) as HP0'.
    pose proof (P1_S _ HP0 HP1) as HP1'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    split.
    + applys_eq (P0_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
    + applys_eq (P1_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
Qed.

Lemma P1'_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(2+(n*2+3)+1) |0> const 0.
Proof.
  pose proof (P_all i) as [HP0 HP1].
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  cbn[Str_app].
  rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM32.


Module TM33.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0LF_0RD0RC_1RE1LA_1LF0LF_0LB0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{B}} [1;1;0] *> r) (at level 30).

Notation "l |0> r" :=
    (l {{C}}> r) (at level 30).

Notation "l |1> r" :=
    (l {{D}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [0] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |0> r.

Definition P1 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [1] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |1> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+6) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(8+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P0 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+4) *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(6+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) /\
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3).
Proof.
  induction i.
  - unfold P0,P1.
    split; es.
  - destruct IHi as [HP0 HP1].
    remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ HP0 HP1) as HP0'.
    pose proof (P1_S _ HP0 HP1) as HP1'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    split.
    + applys_eq (P0_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
    + applys_eq (P1_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
Qed.

Lemma P1'_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(2+(n*2+3)+1) |0> const 0.
Proof.
  pose proof (P_all i) as [HP0 HP1].
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  cbn[Str_app].
  rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM33.


Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC0RB_1RD1LE_1LE0LE_1LA0LC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [1;1;0] *> r) (at level 30).

Notation "l |0> r" :=
    (l {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l {{C}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [0] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |0> r.

Definition P1 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [1] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |1> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+6) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(8+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P0 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+4) *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(6+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) /\
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3).
Proof.
  induction i.
  - unfold P0,P1.
    split; es.
  - destruct IHi as [HP0 HP1].
    remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ HP0 HP1) as HP0'.
    pose proof (P1_S _ HP0 HP1) as HP1'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    split.
    + applys_eq (P0_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
    + applys_eq (P1_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
Qed.

Lemma P1'_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(2+(n*2+3)+0) |0> const 0.
Proof.
  pose proof (P_all i) as [HP0 HP1].
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  cbn[Str_app].
  rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM34.


Module TM35.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_1RD1LF_1LE0LE_0LA0LC_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [1;1;0] *> r) (at level 30).

Notation "l |0> r" :=
    (l {{B}}> r) (at level 30).

Notation "l |1> r" :=
    (l {{C}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [0] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |0> r.

Definition P1 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(2+m) *> [0]^^b *> [1] *> r -->*
  l <* <[1;0]^^c <* [0]^^(2+d+m) |1> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+6) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S n:
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3) ->
  P1 (n*4+13) (n*4+11) (n*2+8) (n*4+12).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+2) *> [0] *> [0]^^(8+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+2) *> [0] *> [1;1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(9+m+n2)) *> [0]^^(n2+2) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+3)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P0 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+4) *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [0] *> r).
  1:{
    es.
  }
  follow HP0.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P1_S' n:
  P0 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*2+5) (n*2+3) (n+4) (n*2+4) ->
  P1 (n*4+13) (n*4+10) (n*2+8) (n*4+11).
Proof.
  unfold P0,P1.
  intros HP0 HP1.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(2+m) *> [0]^^(n2+3) *> [0] *> [0]^^(6+n2) *> [1] *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(2+0) *> [0]^^(n2+3) *> [1] *> [1;0] *> [1]^^(9+m+n2) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    subst. es.
  }
  follow HP1.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^(2+(7+m+n2)) *> [0]^^(n2+3) *> [1] *> r).
  1:{
    es.
  }
  follow HP1.
  replace (2+(n2+4)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+2) (n+4) (n*2+3) /\
  P1 (n*2+5) (n*2+2) (n+4) (n*2+3).
Proof.
  induction i.
  - unfold P0,P1.
    split; es.
  - destruct IHi as [HP0 HP1].
    remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ HP0 HP1) as HP0'.
    pose proof (P1_S _ HP0 HP1) as HP1'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    split.
    + applys_eq (P0_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
    + applys_eq (P1_S' ((n*2+1)*4)); try lia.
      * applys_eq HP0'; lia.
      * applys_eq HP1'; lia.
Qed.

Lemma P1'_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(2+(n*2+3)+0) |0> const 0.
Proof.
  pose proof (P_all i) as [HP0 HP1].
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  cbn[Str_app].
  rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM35.


Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC1LE_1LD0RC_0LF0LB_0LA---_0RF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(m) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m) |> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5) ->
  P0 (n*4+13) (n*4+13) (n*2+8) (n*4+14).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+4) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+4) *> [0;1;0] *> [1]^^(7+m+n2) *> [0]^^(n2+7) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((9+m+n2)) *> [0]^^(n2+4) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+5)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+5) (n+4) (n*2+6) ->
  P0 (n*4+13) (n*4+12) (n*2+8) (n*4+13).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+5) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+5) *> [1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((7+m+n2)) *> [0]^^(n2+5) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+6)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' ((n*2+1)*4)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^((n*2+5)+0) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM36.


Module TM37.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC1LE_1LD1RC_0LB1RF_0LA---_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(m) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m) |> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5) ->
  P0 (n*4+13) (n*4+13) (n*2+8) (n*4+14).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+4) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+4) *> [0;1;0] *> [1]^^(7+m+n2) *> [0]^^(n2+7) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((9+m+n2)) *> [0]^^(n2+4) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+5)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+5) (n+4) (n*2+6) ->
  P0 (n*4+13) (n*4+12) (n*2+8) (n*4+13).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+5) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+5) *> [1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((7+m+n2)) *> [0]^^(n2+5) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+6)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' ((n*2+1)*4)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^((n*2+5)+0) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM37.


Module TM38.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1LD_1LA1RE_0LA0LB_0RF---_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(m) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m) |> r.

Lemma P0_S n:
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5) ->
  P0 (n*4+13) (n*4+13) (n*2+8) (n*4+14).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+4) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+4) *> [0;1;0] *> [1]^^(7+m+n2) *> [0]^^(n2+7) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((9+m+n2)) *> [0]^^(n2+4) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+5)+(9+m+n2)) with (14+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n:
  P0 (n*2+5) (n*2+5) (n+4) (n*2+6) ->
  P0 (n*4+13) (n*4+12) (n*2+8) (n*4+13).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m) *> [0]^^(n2+5) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0) *> [0]^^(n2+5) *> [1;0] *> [1]^^(8+m+n2) *> [0]^^(n2+5) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((7+m+n2)) *> [0]^^(n2+5) *> r).
  1:{
    es.
  }
  follow HP0.
  replace ((n2+6)+(7+m+n2)) with (13+n2+n2+m) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' ((n*2+1)*4)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^((n*2+5)+0) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM38.


Module TM39.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1LD_1LA0RE_0LA0LB_0RB0RF_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(m*3) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m*3) |> r.

Lemma P0_S n0:
  let n:=n0*3 in
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5) ->
  P0 (n*4+13) (n*4+13) (n*2+8) (n*4+14).
Proof.
  cbn.
  remember (n0*3) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m*3) *> [0]^^(n2+4) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0*3) *> [0]^^(n2+4) *> [0;1;0] *> [1]^^(7+m*3+n2) *> [0]^^(n2+7) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((3+m+n0*2)*3) *> [0]^^(n2+4) *> r).
  1:{
    replace (7+m*3+n2) with (7+(m+n0*2)*3) by lia.
    remember (m+n0*2) as v1.
    replace ((3+m+n0*2)*3) with (9+v1*3) by lia.
    es.
  }
  follow HP0.
  replace ((n2+5)+(3+m+n0*2)*3) with (14+n2+n2+m*3) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n0:
  let n:=n0*3+1 in
  P0 (n*2+5) (n*2+5) (n+4) (n*2+6) ->
  P0 (n*4+13) (n*4+12) (n*2+8) (n*4+13).
Proof.
  cbn.
  remember (n0*3+1) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+5) <| [1]^^(m*3) *> [0]^^(n2+5) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n2+5) <| [1]^^(0*3) *> [0]^^(n2+5) *> [1;0] *> [1]^^(8+m*3+n2) *> [0]^^(n2+5) *> r).
  1:{
    subst. es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+5) <| [1]^^((3+m+n0*2)*3) *> [0]^^(n2+5) *> r).
  1:{
    replace (8+m*3+n2) with (10+(m+n0*2)*3) by lia.
    remember (m+n0*2) as v1.
    replace ((3+m+n0*2)*3) with (9+v1*3) by lia.
    es.
  }
  follow HP0.
  replace ((n2+6)+(3+m+n0*2)*3) with (13+n2+n2+m*3) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma pow4_mod3 i:
  exists a,
  (2^(i*2)-1) = a*3.
Proof.
  induction i.
  1: exists O; cbn; lia.
  destruct IHi as [a H].
  cbn.
  pose proof (Nat.pow_nonzero 2 (i*2)).
  exists (a*4+1).
  lia.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+5) (n*2+4) (n+4) (n*2+5).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (pow4_mod3 i) as [a Ha].
    cbn in IHi.
    replace (n*4) with (a*4*3) in IHi by lia.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' (a*8+1)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^((n*2+5)+0*3) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM39.


Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC0RB_0LD1LE_1LD0LE_1RB0LA_---0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{E}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM40.


Module TM41.
Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC0RB_0LD1LE_1LD0LE_1RB0LA_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{E}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM41.


Module TM42.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1RB0LF_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM42.


Module TM43.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_0LD1LE_1LD0LA_1RB0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM43.


Module TM44.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RD0LF_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM44.


Module TM45.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC0RB_0LD1LA_1LD0LA_1RD0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{A}} [0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{C}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2+1) <| [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m+2) |> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  mid (l <* [0]^^(n'+1) <* [0]^^n' <| [1]^^m *> [0]^^n' *> [0]^^(n'+1) *> r).
  1:{
    replace (n'*2) with (n'+n') by lia.
    es.
  }
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n' <| [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n' <| [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (n2+0+2) with (2+n2) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0+2) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM45.


Module TM46.
Definition tm := Eval compute in (TM_from_str "1RB0LF_0LC1RE_1LC1LD_1RB0LA_0RB0RE_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{E}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM46.


Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB0LE_0LC1RD_1LC1LA_0RB0RD_1LA0LF_---0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{D}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [1]^^m *> [0]^^(n*2+1) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 3 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  rewrite (lpow_add _ n' (n'+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [1]^^0 *> [0]^^n' *> [1]^^(2+m+n2) *> [0]^^(n'+1) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [1]^^(2+m+n2) *> [0]^^(n') *> r).
  1:{
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM47.


Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC1RE_0LC1LD_1RB0LA_0RE0RB_---0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
    (l <* [1;1] {{E}}> r) (at level 30).

Notation "l |1> r" :=
    (l <* [0] {{B}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*2) |> [0]^^m *> [1] *> [0]^^(n*2) *> r -->*
  l <* [1]^^(n*2+2) <* [0]^^(n*2+m) |1> r.

Lemma P1'_S n0:
  P1' (n0*3) ->
  P1' ((n0*3)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  rewrite (lpow_add _ n2 (n2+2)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [0]^^0 *> [1] *> [0]^^n2 *> [1] *> [0]^^(1+m+n2) *> [1] *> [0]^^(n') *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    replace n2 with (n0*2*3) by lia.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [0]^^(2+m+n2) *> [1] *> [0]^^(n2) *> r).
  1:{
    replace (1+m+n2) with (1+(m+n2)) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma P1'_S' n0:
  P1' (n0*3+1) ->
  P1' ((n0*3+1)*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n0*3+1) as n.
  remember (n*2) as n2.
  remember (n2+1) as n'.
  replace ([0]^^(n'*2)) with ([0]^^(n2+(n2+2))) by (f_equal; lia).
  replace (n'*2+1) with (n'+(n'+1)) by lia.
  rewrite (lpow_add _ n2 (n2+2)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n'+1) with (1+n') by lia.
  mid (l <* [0]^^n2 |> [0]^^0 *> [1] *> [0]^^n2 *> [1] *> [0]^^(1+m+n2) *> [1] *> [0]^^(n') *> r).
  1:{
    simpl_tape.
    er. sr.
    er. sr.
    er.
    replace n2 with (2+n0*2*3) by lia.
    simpl_tape.
    rewrite lpow_mul.
    er. sr.
    do 5 step1.
    subst n' n2 n.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [1]^^(n2+2) <* [0]^^n2 |> [0]^^(2+m+n2) *> [1] *> [0]^^(n2) *> r).
  1:{
    replace (1+m+n2) with (1+(m+n2)) by lia.
    replace (2+m+n2) with (2+(m+n2)) by lia.
    remember (m+n2) as v1.
    replace n' with (1+n2) by lia.
    es.
  }
  follow HP1'.
  replace (n2+(2+m+n2)) with (n'*2+m) by lia.
  replace n' with (1+n+n) by lia.
  subst n' n2.
  es.
Qed.

Lemma pow2_mod3 i:
  exists a, (2^i-1) = a*3 \/ (2^i-1) = a*3+1.
Proof.
  induction i.
  - exists O; cbn; lia.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    destruct IHi as [a [H|H]].
    + eexists (a*2); cbn; lia.
    + eexists (a*2+1); cbn; lia.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - pose proof (Nat.pow_nonzero 2 i) as Hpow.
    pose proof (pow2_mod3 i) as [a [H|H]].
    + applys_eq (P1'_S a).
      2: applys_eq IHi; lia.
      cbn; lia.
    + applys_eq (P1'_S' a).
      2: applys_eq IHi; lia.
      cbn; lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*2+2) <* [0]^^((2^i-1)*2+0) |1> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM48.


Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LB1LA_0LD0LA_0LE---_1RE1LF_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{C}} [0;1;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P1' n :=
  forall m l r,
  l <* [0]^^(n*8+3) <| [1]^^m *> [0]^^(n*4+1) *> r -->*
  l <* [1]^^(n*4+3) <* [0]^^(n*8+m+4) |> r.

Lemma P1'_S n:
  P1' n ->
  P1' (n*2+1).
Proof.
  unfold P1'.
  intro HP1'.
  intros.
  remember (n*2+1) as n'.
  remember (n*8) as n8.
  remember (n*4) as n4.
  replace (n'*8+3) with (n8+3+(n8+8)) by lia.
  replace (n'*4+1) with (n4+1+(n4+4)) by lia.
  rewrite (lpow_add _ (n8+3)).
  rewrite (lpow_add _ (n4+1)).
  repeat rewrite Str_app_assoc.
  follow HP1'.
  replace (n4+4) with (4+n4) by lia.
  mid (l <* [0]^^3 <* [0]^^(n8+3) <| [1]^^0 *> [0]^^(n4+1) *> [1]^^(6+m+n8) *> [0]^^(n4+3) *> r).
  1:{
    er. sr.
    er. sr.
    er.
    replace n4 with (n*2*2) by lia.
    rewrite lpow_mul.
    er. sr.
    do 6 step1.
    subst n' n8 n4.
    finish.
    tape_eq.
  }
  follow HP1'.
  mid (l <* [0]^^3 <* [1]^^(n4+3) <* [0]^^(n8+3) <| [1]^^(4+m+n8) *> [0]^^(n4+1) *> [0]^^2 *> r).
  1:{
    es.
  }
  follow HP1'.
  replace (n'*8+m) with (8+n8+m+n8) by lia.
  replace n8 with (n4+n4) by lia.
  replace n' with (1+n+n) by lia.
  subst n4.
  es.
Qed.

Lemma P1'_all i:
  P1' (2^i-1).
Proof.
  induction i.
  - unfold P1'; es.
  - cbn.
    pose proof (Nat.pow_nonzero 2 i) as Hpow.
    applys_eq (P1'_S (2^i-1) IHi).
    lia.
Qed.

Lemma P1'_all' i:
  c0 -->*
  const 0 <* [1]^^((2^i-1)*4+3) <* [0]^^((2^i-1)*8+0+4) |> const 0.
Proof.
  eapply evstep_trans.
  2: apply P1'_all.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P1'_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n n).
  lia.
Qed.

End TM49.

Lemma lpow_fold_1 (a:Sym) n r:
  a >> [a]^^n *> r =
  [a]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  cbn.
  rewrite lpow_rotate.
  reflexivity.
Qed.

Lemma lpow_fold_2 (a b:Sym) n r:
  a >> b >> [a;b]^^n *> r =
  [a;b]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 2 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_fold_3 (a b c:Sym) n r:
  a >> b >> c >> [a;b;c]^^n *> r =
  [a;b;c]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 3 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Ltac fold_tape :=
  repeat rewrite lpow_fold_1;
  repeat rewrite lpow_fold_2;
  repeat rewrite lpow_fold_3.


Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1LD_1LA0RF_0LA0LE_0LC1LD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{D}} [0;0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [0;0;1]^^(m) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m*3) |> r.

Lemma P0_S n0:
  let n:=n0*3 in
  P0 (n*2+4) (n*2+1) (n+4) (n*2+2) ->
  P0 (n*4+12) (n*4+10) (n*2+8) (n*4+11).
Proof.
  cbn.
  remember (n0*3) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+4) <| [0;0;1]^^(m) *> [0]^^(n2+1) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  replace (n2+2+m*3) with (2+(n0*2+m)*3) by lia.
  mid (l <* [0]^^(n2+4) <| [0;0;1]^^(1) *> [0]^^(n2+1) *> [0;1;0;1] *> [0;0;1]^^(1+n0*2+m) *> [0]^^(n2+7) *> r).
  1:{
    er.
    rewrite lpow_mul.
    sr.
    er. sr.
    do 31 step1.
    subst.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+4) <| [0;0;1]^^(3+n0*2+m) *> [0]^^(n2+1) *> r).
  1:{
    remember (1+n0*2+m) as v1.
    replace (3+n0*2+m) with (2+v1) by lia.
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    do 3 step1.
    finish.
  }
  follow HP0.
  replace ((n2+2)+(3+n0*2+m)*3) with (11+n2+n2+m*3) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n0:
  let n:=n0*3+1 in
  P0 (n*2+4) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+12) (n*4+9) (n*2+8) (n*4+10).
Proof.
  cbn.
  remember (n0*3+1) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+4) <| [0;0;1]^^(m) *> [0]^^(n2+2) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  replace (n2+3+m*3) with (5+(n0*2+m)*3) by lia.
  mid (l <* [0]^^(n2+4) <| [0;0;1]^^(1) *> [0]^^(n2+2) *> [1;0;1] *> [0;0;1]^^(2+n0*2+m) *> [0]^^(n2+5) *> r).
  1:{
    er.
    rewrite lpow_mul.
    sr.
    er. sr.
    do 31 step1.
    subst.
    finish.
    repeat rewrite Nat.mul_add_distr_r.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+4) <| [0;0;1]^^((3+m+n0*2)) *> [0]^^(n2+2) *> r).
  1:{
    remember (2+n0*2+m) as v1.
    replace (3+m+n0*2) with (v1+1) by lia.
    replace (n2+3+1*3) with (6+n2) by lia.
    er. sr.
    er. sr.
    do 3 step1.
    finish.
  }
  follow HP0.
  rewrite merge_lpow.
  finish.
Qed.

Lemma pow4_mod3 i:
  exists a,
  (2^(i*2)-1) = a*3.
Proof.
  induction i.
  1: exists O; cbn; lia.
  destruct IHi as [a H].
  cbn.
  pose proof (Nat.pow_nonzero 2 (i*2)).
  exists (a*4+1).
  lia.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+4) (n*2+1) (n+4) (n*2+2).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (pow4_mod3 i) as [a Ha].
    cbn in IHi.
    replace (n*4) with (a*4*3) in IHi by lia.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' (a*8+1)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(n*2+2+1*3) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM50.


Module TM51.
Definition tm := Eval compute in (TM_from_str "1RB0LD_0RC1LD_1LA0RF_0LA0LE_0LC1LF_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{D}} [0;0;1;0;1] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [0;0;1]^^(m) *> [0]^^b *> r -->*
  l <* <[1;0]^^c <* [0]^^(d+m*3) |> r.

Lemma P0_S n0:
  let n:=n0*3 in
  P0 (n*2+4) (n*2+1) (n+4) (n*2+2) ->
  P0 (n*4+12) (n*4+10) (n*2+8) (n*4+11).
Proof.
  cbn.
  remember (n0*3) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+4) <| [0;0;1]^^(m) *> [0]^^(n2+1) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  replace (n2+2+m*3) with (2+(n0*2+m)*3) by lia.
  mid (l <* [0]^^(n2+4) <| [0;0;1]^^(1) *> [0]^^(n2+1) *> [0;1;0;1] *> [0;0;1]^^(1+n0*2+m) *> [0]^^(n2+7) *> r).
  1:{
    er.
    rewrite lpow_mul.
    sr.
    er. sr.
    subst.
    es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+4) <| [0;0;1]^^(3+n0*2+m) *> [0]^^(n2+1) *> r).
  1:{
    remember (1+n0*2+m) as v1.
    replace (3+n0*2+m) with (2+v1) by lia.
    es.
  }
  follow HP0.
  replace ((n2+2)+(3+n0*2+m)*3) with (11+n2+n2+m*3) by lia.
  replace n4 with (n2+n2) by lia.
  replace n2 with (n+n) by lia.
  es.
Qed.

Lemma P0_S' n0:
  let n:=n0*3+1 in
  P0 (n*2+4) (n*2+2) (n+4) (n*2+3) ->
  P0 (n*4+12) (n*4+9) (n*2+8) (n*4+10).
Proof.
  cbn.
  remember (n0*3+1) as n.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n2+8) <* [0]^^(n2+4) <| [0;0;1]^^(m) *> [0]^^(n2+2) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  replace (n2+3+m*3) with (5+(n0*2+m)*3) by lia.
  mid (l <* [0]^^(n2+4) <| [0;0;1]^^(1) *> [0]^^(n2+2) *> [1;0;1] *> [0;0;1]^^(2+n0*2+m) *> [0]^^(n2+5) *> r).
  1:{
    er.
    rewrite lpow_mul.
    sr.
    subst.
    repeat rewrite Nat.mul_add_distr_r.
    es.
  }
  follow HP0.
  mid (l <* [0;1]^^(n+4) <* [0]^^(n2+4) <| [0;0;1]^^((3+m+n0*2)) *> [0]^^(n2+2) *> r).
  1:{
    remember (2+n0*2+m) as v1.
    replace (3+m+n0*2) with (v1+1) by lia.
    replace (n2+3+1*3) with (6+n2) by lia.
    es.
  }
  follow HP0.
  rewrite merge_lpow.
  finish.
Qed.

Lemma pow4_mod3 i:
  exists a,
  (2^(i*2)-1) = a*3.
Proof.
  induction i.
  1: exists O; cbn; lia.
  destruct IHi as [a H].
  cbn.
  pose proof (Nat.pow_nonzero 2 (i*2)).
  exists (a*4+1).
  lia.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n*2+4) (n*2+1) (n+4) (n*2+2).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    pose proof (pow4_mod3 i) as [a Ha].
    cbn in IHi.
    replace (n*4) with (a*4*3) in IHi by lia.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' (a*8+1)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[1;0]^^(n+4) <* [0]^^(n*2+2+1*3) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM51.


Module TM52.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC0LA_1LD1RF_0RA0LE_0LD---_0RB0RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
    (l <{{E}} [0;1;1;0] *> r) (at level 30).

Notation "l |> r" :=
    (l {{B}}> r) (at level 30).

Definition P0 a b c d :=
  forall m l r,
  l <* [0]^^a <| [1]^^(4+m) *> [0]^^b *> r -->*
  l <* <[0;1]^^c <* [0]^^(d+m) |> r.

Lemma P0_S n:
  P0 (n+2) (n*2+1) (n+4) (n+3) ->
  P0 (n*2+6) (n*4+10) (n*2+8) (n*2+8).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n+4) <* [0]^^(n+2) <| [1]^^(4+m) *> [0]^^(n2+1) *> [0]^^(9+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    replace n2 with (n+n) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n+2) <| [1]^^(4+0) *> [0]^^(n2+1) *> [0] *> [1]^^(5+m+n) *> [0]^^(n2+7) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    do 38 step1.
    subst.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* <[0;1]^^(n+4) <* [0]^^(n+2) <| [1]^^(4+(5+m+n)) *> [0]^^(n2+1) *> r).
  1:{
    remember (m+n) as v1.
    replace (5+m+n) with (5+v1) by lia.
    er. sr.
    er. sr.
    er. sr.
    er. sr.
    do 12 step1.
    finish.
  }
  follow HP0.
  rewrite merge_lpow.
  finish.
Qed.

Lemma P0_S' n:
  P0 (n+2) (n*2+2) (n+4) (n+4) ->
  P0 (n*2+6) (n*4+9) (n*2+8) (n*2+7).
Proof.
  unfold P0.
  intros HP0.
  intros.
  remember (n*2) as n2.
  remember (n*4) as n4.
  mid (l <* [0]^^(n+4) <* [0]^^(n+2) <| [1]^^(4+m) *> [0]^^(n2+2) *> [0]^^(7+n2) *> r).
  1:{
    replace n4 with (n2+n2) by lia.
    replace n2 with (n+n) by lia.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* [0]^^(n+2) <| [1]^^(4+0) *> [0]^^(n2+2) *> [1]^^(6+m+n) *> [0]^^(n2+5) *> r).
  1:{
    er. sr.
    er. sr.
    er. sr.
    do 38 step1.
    subst.
    finish.
    tape_eq.
  }
  follow HP0.
  mid (l <* <[0;1]^^(n+4) <* [0]^^(n+2) <| [1]^^(4+(3+m+n)) *> [0]^^(n2+2) *> r).
  1:{
    remember (m+n) as v1.
    replace (6+m+n) with (6+v1) by lia.
    replace (3+m+n) with (3+v1) by lia.
    rewrite (Nat.add_comm n 4).
    er. sr.
    er. sr.
    do 12 step1.
    finish.
  }
  follow HP0.
  rewrite merge_lpow.
  finish.
Qed.

Lemma P_all i:
  let n:=(2^(i*2)-1)*4 in
  P0 (n+2) (n*2+1) (n+4) (n+3).
Proof.
  induction i.
  - unfold P0.
    es.
  - remember (2^(i*2)-1) as n.
    pose proof (Nat.pow_nonzero 2 (i*2)) as Hpow.
    cbn in IHi.
    pose proof (P0_S _ IHi) as HP0'.
    replace ((2^(S i*2)-1)) with (n*4+3) by (cbn; lia).
    cbn.
    applys_eq (P0_S' (n*8+4)); try lia.
    applys_eq HP0'; lia.
Qed.

Lemma P_all' i:
  let n:=(2^(i*2)-1)*4 in
  c0 -->*
  const 0 <* <[0;1]^^(n+4) <* [0]^^(n+3+0) |> const 0.
Proof.
  pose proof (P_all i) as HP0.
  unfold P0 in HP0.
  eapply evstep_trans.
  2: apply HP0.
  rewrite lpow_all0.
  2: solve_const0_eq.
  rewrite lpow_all0.
  2: solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  eexists _,_.
  split.
  1: apply (P_all' n).
  split.
  1: solve_sigma_score.
  pose proof (Sn_le_pow2n (n*2)).
  lia.
Qed.

End TM52.


