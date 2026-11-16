From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require ES_v2.

Ltac es_v2 := ES_v2.es.


Open Scope list.

Ltac unfold_config' :=
match goal with
| |- ?a -[_]->* ?b -> _ =>
  unfold_config_expr a;
  unfold_config_expr b
end.

Ltac follow' x :=
  pose proof x as Hx;
  gen Hx;
  unfold_config';
  simpl_rotate;
  intro Hx;
  try (
  follow Hx;
  clear Hx).


Ltac solve_sigma_score' f :=
  eapply sigma_score_unbounded_nonhalt;
  intros n;
  eexists _,_;
  split;
  [ apply (f n) |];
  split;
  [ solve_sigma_score |];
  lia.

Ltac simpl_nat :=
  repeat rewrite Nat.add_succ_r;
  repeat rewrite <-Nat.mul_add_distr_l;
  repeat rewrite <-Nat.mul_succ_r.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RB0RC_0RD1RF_1LE1RD_0LF1RB_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [0;1;0;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*2+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[1;0]^^(2+n) <* [0] <* [1]^^(2+n*3) <{{A}} r -->*
  l <{{B}} [1;0] *> [1]^^(1+n) *> [0;1;0;1]^^(1+n) *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 3 step1.
  follow' (IHn ([0;1]*>l) ([0;0;0]*>r)).
  es.
  follow' (Incs1 2 (2+n) n ([1]*>l) ([0;0;0]*>r)).
  do 7 step1.
  simpl_rotate.
  step1.
  rewrite lpow_add'.
  follow' (IHn ([1]*>l) ([0;1;0;1]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* <[1;0]^^(2+n) <* [0] <* [1]^^(2+n*3) <{{A}} [1;0;1] *> 0inf.
Proof.
  induction n.
  1: es.
  follow IHn; clear IHn.
  follow' (P0_n n (0inf) ([1;0;1]*>0inf)).
  es. er.
  follow' (Incs1 2 (2+n) n (0inf) ([1;0;1]*>0inf)).
  replace (n*2+(S(S n))) with (2+n*3) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RD_0LC1LA_---1RE_1RF1RE_0RB1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{E}}> [0;1;1]^^c *> r.
Definition S2 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{E}}> [1;0;1;0;1;0;1]^^c *> r.
Definition S3 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{F}}> [1;0;1;1;0;1;0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*2+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (3+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*3+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (3+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c*3+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0]^^(2+n*4) <* [1]^^(4+n*6) <{{A}} r -->*
  l <{{A}} [0;1;1]^^(1+n) *> [1] *> [0;1;0;1;0;1;1]^^n *> [0;1] *> r.

Definition P1 n :=
  forall l r,
  l <* <[0]^^(4+n*4) <* [1]^^(7+n*6) <{{A}} r -->*
  l <{{A}} [0] *> [0;1;1]^^(1+n) *> [1] *> [0;1;0;1;0;1;1]^^n *> [0;1;0;1;0;1] *> r.

Lemma P0_S n:
  P1 n ->
  P0 (1+n).
Proof.
  unfold P0,P1.
  intros HP1 l r.
  cbn.
  do 3 step1.
  follow' (HP1 ([0;0]*>l) ([0;0;0]*>r)).
  es; er.
  follow' (Incs1 1 2 n ([1]*>l) ([1;0;1;0;1;0;1]^^(1+n)*>[0;0;0]*>r)).
  es; er.
  follow' (Incs2 (4+n) (6+n*2) n ([1]*>l) ([0;0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 5 step1.
  follow' (HP1 ([0;1]*>l) ([1;0;1]*>r)).
  es.
Qed.

Lemma P1_S n:
  P0 n ->
  P1 n.
Proof.
  unfold P0,P1.
  intros HP0 l r.
  cbn.
  do 3 step1.
  follow' (HP0 ([0;0]*>l) ([0;0;0]*>r)).
  es; er.
  follow' (Incs1 0 2 n ([1]*>l) ([1;0;1;0;1;0;1]^^(n)*>[1;0;1;0;0;0]*>r)).
  es; er.
  follow' (Incs3 (1+n) (5+n*2) n ([1]*>l) ([0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 5 step1.
  follow' (HP0 ([1]*>l) ([0;1;0;1]*>r)).
  es.
Qed.

Lemma P_n n:
  P0 n /\ P1 n.
Proof.
  induction n.
  1: unfold P0,P1; split; es.
  pose proof (P0_S n) as HP0.
  pose proof (P1_S (S n)) as HP1.
  cbn in HP0.
  tauto.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1] <* <[0]^^(2+n*4) <* [1]^^(4+n*6) <{{A}} [0;1;0;1] *> 0inf.
Proof.
  induction n.
  1: es.
  follow IHn; clear IHn.
  cbn.
  pose proof (P_n n) as [HP0 HP1].
  unfold P0 in HP0.
  follow HP0.
  clear HP0.
  es; er.
  follow (Incs1 1 2 n).
  es; er.
  cbn.
  follow' (Incs2 (4+n) (6+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 5 step1.
  unfold P1 in HP1.
  follow' (HP1 ([0;1]*>0inf) ([1;0;1]*>0inf)).
  clear HP1.
  es; er.
  follow (Incs1 1 4 n).
  es; er.
  follow' (Incs3 (5+n) (11+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB---_0RC1LB_1LD0RF_0LE0LD_0RF1RC_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[0]^^(1+a) <* [1]^^b {{F}}> [0;0;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*2+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Definition P0 n :=
  forall l r,
  l <* [0]^^(2+n) <* [1]^^(3+n*4) <{{D}} r -->*
  l <{{E}} [0] *> [0;0;1]^^(1+n) *> [1]^^(1+n*2) *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 4 step1.
  follow' (IHn ([0]*>l) ([0;0;0;0]*>r)).
  es; er.
  follow (Incs1 1 0 n).
  unfold S1; cbn.
  er. sr.
  do 7 step1.
  change [1;1] with ([1]^^2).
  rewrite <-lpow_mul,lpow_add'.
  simpl_nat.
  cbn.
  follow' (IHn ([1;1;0]*>l) ([1;1]*>r)).
  es.
Qed.

Definition S0 a b :=
  0inf <* [1;1] <* [0]^^a <* [1]^^b <{{D}} [1;1] *> 0inf.

Ltac follow_Incs1 b c :=
    follow (Incs1 0 b c);
    unfold S1;
    rewrite <-Nat.mul_assoc;
    er; sr;
    rewrite lpow_add';
    simpl_nat.

Ltac follow_P0_n a l r :=
  follow' (P0_n a l r);
  rewrite <-Nat.mul_assoc;
  er.

Lemma BigStep n:
  c0 -->*
  S0 (8+n*7) (23+n*28).
Proof.
  induction n.
  1: unfold S0; cbn; solve_init.
  follow IHn; clear IHn.
  mid (S0 (10+n*7) (30+n*28)).
  1:{
    unfold S0.
    follow_P0_n (5+n*7) ([0;1;1]*>0inf) ([1;1]*>0inf).
    follow_Incs1 10 (n*7).
    do 9 step1.
    follow_P0_n (5+n*7) ([1;1;0;1;1]*>0inf) ([0;0;1;1]*>0inf).
    follow_Incs1 14 (n*7).
    es.
  }
  mid (S0 (12+n*7) (41+n*28)).
  1:{
    unfold S0.
    do 3 step1.
    follow_P0_n (6+n*7) ([0;0;1;1]*>0inf) ([0;0;0;1;1]*>0inf).
    follow_Incs1 12 (n*7).
    do 29 step1.
    follow_P0_n (6+n*7) ([1;1;0;0;1;1]*>0inf) ([1;0;0;1;1;1;1]*>0inf).
    follow_Incs1 14 (n*7).
    er. sr.
    er. sr.
    do 7 step1.
    follow_P0_n (8+n*7) ([1;1;0;1;1]*>0inf) ([1;1]*>0inf).
    follow_Incs1 20 (n*7).
    er.
  }
  unfold S0.
  do 2 step1.
  follow_P0_n (9+n*7) ([0;1;1]*>0inf) ([0;0;1;1]*>0inf).
  follow_Incs1 18 (n*7).
  er. sr.
  er. sr.
  do 10 step1.
  follow_P0_n (9+n*7) ([0;1;1;0;1;1]*>0inf) ([0;0;0;1;1]*>0inf).
  follow_Incs1 18 (n*7).
  do 29 step1.
  follow_P0_n (9+n*7) ([1;1;0;1;1;0;1;1]*>0inf) ([1;0;0;1;1;1;1]*>0inf).
  follow_Incs1 24 (n*7).
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LA_1RF0RD_1RE1RD_0RC1LE_1LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [0;1;1]^^c *> r.
Definition S2 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [1;1;0;1;0;1;1;0;1]^^c *> r.
Definition S3 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{E}}> [1;1;0;1;1;1;0;1;0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*2+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (3+a) (6+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*3+a) (c*6+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (3+a) (6+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c*3+a) (c*6+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0]^^(2+n*4) <* [1]^^(4+n*8) <{{A}} r -->*
  l <{{A}} [1;1;0]^^n *> [1] *> [1;1;1;0;1;0;1;1;0]^^n *> [1;1;1;0;1] *> r.

Definition P1 n :=
  forall l r,
  l <* <[0]^^(4+n*4) <* [1]^^(8+n*8) <{{A}} r -->*
  l <{{A}} [0;1;1]^^(1+n) *> [1;1;0;1;0;1;1;0;1]^^(1+n) *> r.

Lemma P0_S n:
  P1 n ->
  P0 (1+n).
Proof.
  unfold P0,P1.
  intros HP1 l r.
  cbn.
  do 4 step1.
  follow' (HP1 ([0;0]*>l) ([0;0;0;0]*>r)).
  es; er.
  follow (Incs1 0 1 n).
  unfold S1.
  es; er.
  follow' (Incs2 (4+n) (7+n*2) n ([1]*>l) ([0;0;0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 7 step1.
  follow' (HP1 ([0;1]*>l) ([1;1;0;1]*>r)).
  es.
Qed.

Lemma P1_S n:
  P0 n ->
  P1 n.
Proof.
  unfold P0,P1.
  intros HP0 l r.
  cbn.
  do 4 step1.
  follow' (HP0 ([0;0]*>l) ([0;0;0;0]*>r)).
  es; er.
  follow (Incs1 0 1 n).
  unfold S1.
  es; er.
  follow' (Incs3 (1+n) (5+n*2) n ([1]*>l) ([0;0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 7 step1.
  follow' (HP0 ([1]*>l) ([0;1;1;0;1]*>r)).
  es.
Qed.

Lemma P_n n:
  P0 n /\ P1 n.
Proof.
  induction n.
  1: unfold P0,P1; split; es.
  pose proof (P0_S n) as HP0.
  pose proof (P1_S (S n)) as HP1.
  cbn in HP0.
  tauto.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1] <* <[0]^^(2+n*4) <* [1]^^(5+n*8) <{{A}} [1;1;0;1] *> 0inf.
Proof.
  induction n.
  1: es.
  follow IHn; clear IHn.
  step1.
  pose proof (P_n n) as [HP0 HP1].
  follow HP0.
  clear HP0.
  es; er.
  follow (Incs1 1 1 n).
  es; er.
  cbn.
  follow' (Incs2 (4+n) (7+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 7 step1.
  unfold P1 in HP1.
  follow' (HP1 ([0;1]*>0inf) ([1;1;0;1]*>0inf)).
  clear HP1.
  es; er.
  follow (Incs1 1 3 n).
  es; er.
  follow' (Incs3 (5+n) (13+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LA_1RF0RD_1RE1RD_0RC1LE_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [0;1;1]^^c *> r.
Definition S2 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [1;1;0;1;1;0;1;1;0;1;1]^^c *> r.
Definition S3 a b c l r := l <* [0]^^a <* [0] <* [1]^^b <* [1] {{E}}> [1;1;0;1;1;1;1;0;1;1;0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (2+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*2+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (3+a) (8+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*3+a) (c*8+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (3+a) (8+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c*3+a) (c*8+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0]^^(2+n*4) <* [1]^^(5+n*10) <{{A}} r -->*
  l <{{A}} [1;1] *> [0;1;1]^^n *> [1;1;0;1;1;0;1;1;0;1;1]^^n *> [1;1;0;1;1] *> r.

Definition P1 n :=
  forall l r,
  l <* <[0]^^(4+n*4) <* [1]^^(10+n*10) <{{A}} r -->*
  l <{{A}} [0;1;1]^^(1+n) *> [1;1;0;1;1;0;1;1;0;1;1]^^(1+n) *> r.

Lemma P0_S n:
  P1 n ->
  P0 (1+n).
Proof.
  unfold P0,P1.
  intros HP1 l r.
  cbn.
  do 5 step1.
  follow' (HP1 ([0;0]*>l) ([0;0;0;0;0]*>r)).
  es; er.
  follow (Incs1 0 1 n).
  unfold S1.
  es; er.
  follow' (Incs2 (4+n) (9+n*2) n ([1]*>l) ([0;0;0;0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 9 step1.
  follow' (HP1 ([0;1]*>l) ([1;1;0;1;1]*>r)).
  es.
Qed.

Lemma P1_S n:
  P0 n ->
  P1 n.
Proof.
  unfold P0,P1.
  intros HP0 l r.
  cbn.
  do 5 step1.
  follow' (HP0 ([0;0]*>l) ([0;0;0;0;0]*>r)).
  es; er.
  follow (Incs1 0 1 n).
  unfold S1.
  es; er.
  follow' (Incs3 (1+n) (6+n*2) n ([1]*>l) ([0;0;0;0]*>r)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 9 step1.
  follow' (HP0 ([1]*>l) ([0;1;1;0;1;1]*>r)).
  es.
Qed.

Lemma P_n n:
  P0 n /\ P1 n.
Proof.
  induction n.
  1: unfold P0,P1; split; es.
  pose proof (P0_S n) as HP0.
  pose proof (P1_S (S n)) as HP1.
  cbn in HP0.
  tauto.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1] <* <[0]^^(2+n*4) <* [1]^^(6+n*10) <{{A}} [1;1;0;1;1] *> 0inf.
Proof.
  induction n.
  1: es.
  follow IHn; clear IHn.
  step1.
  pose proof (P_n n) as [HP0 HP1].
  follow HP0.
  clear HP0.
  es; er.
  follow (Incs1 1 1 n).
  es; er.
  cbn.
  follow' (Incs2 (4+n) (9+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  do 9 step1.
  unfold P1 in HP1.
  follow' (HP1 ([0;1]*>0inf) ([1;1;0;1;1]*>0inf)).
  clear HP1.
  es; er.
  follow (Incs1 1 3 n).
  es; er.
  follow' (Incs3 (5+n) (16+n*2) n ([1]*>0inf) (0inf)).
  rewrite lpow_mul in Hx.
  follow' Hx.
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0LB_1RD0RF_0RE1LD_1LE1LB_---0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{D}}> [1;1;1;0;0;0]^^c *> r.
Definition S2 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{B}}> [0;0;1;1;1;0]^^c *> r.
Definition S3 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{A}}> [1;0;0;0;1;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0;1]^^n <* [0;0] <* [1]^^(3+n*5) <{{B}} r -->*
  l <{{D}} [1]^^(5+n) *> [0;0;0;1;1;1]^^n *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 5 step1.
  follow' (IHn ([1;0]*>l) ([0;0;0;0;0]*>r)).
  es. er.
  follow' (Incs1 1 (6+n) n (l) ([0;0]*>r)).
  simpl_nat.
  do 7 step1.
  simpl_rotate.
  follow' (IHn ([1]*>l) ([0;0;0;1;1;1]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* <[1;0]^^(3+n) <* [0] <* [1]^^(14+n*5) <{{B}} [1;1;1] *> 0inf.
Proof.
  induction n.
  1: solve_init.
  follow IHn; clear IHn.
  step1.
  follow' (P0_n (2+n) ([1;0]*>0inf) ([0;1;1;1]*>0inf)).
  es; er.
  follow' (Incs2 3 (14+n) n (0inf) ([1;1;1]*>0inf)).
  simpl_nat.
  cbn.
  do 3 step1.
  follow' (P0_n (2+n) ([1;0]*>0inf) ([0;0;0;1;1]*>0inf)).
  es; er.
  follow' (Incs3 4 (16+n) n (0inf) (0inf)).
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{C}}> [1;1;1;0;0;0]^^c *> r.
Definition S2 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{F}}> [0;0;0;1;1;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0;1]^^n <* [0;0] <* [1]^^(3+n*5) <{{A}} r -->*
  l <{{C}} [1]^^(5+n) *> [0;0;0;1;1;1]^^n *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 5 step1.
  follow' (IHn ([1;0]*>l) ([0;0;0;0;0]*>r)).
  es. er.
  follow' (Incs1 1 (6+n) n (l) ([0;0]*>r)).
  simpl_nat.
  do 7 step1.
  simpl_rotate.
  follow' (IHn ([1]*>l) ([0;0;0;1;1;1]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* <[1;0]^^(12+n) <* [0] <* [1]^^(63+n*5) <{{A}} [1;1;1] *> 0inf.
Proof.
  induction n.
  1: subst; solve_init.
  follow IHn; clear IHn.
  remember (12+n) as n'.
  replace (12+S n) with (1+n') by lia.
  replace (63+n*5) with (3+n'*5) by lia.
  replace (63+S n*5) with (8+n'*5) by lia.
  follow' (P0_n (n') (0inf) ([1;1;1]*>0inf)).
  es; er.
  follow' (Incs2 1 (2+n') n' (0inf) ([1;1;1]*>0inf)).
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC1LB_1LC1LD_1RA0LD_---0RF_1RD1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{B}}> [1;1;1;0;0;0]^^c *> r.
Definition S2 a b c l r := l <* <[1;0]^^a <* [0] <* [1]^^b <* [1] {{F}}> [0;0;0;1;1;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (1+a) (4+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c+a) (c*4+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0;1]^^n <* [0;0] <* [1]^^(3+n*5) <{{D}} r -->*
  l <{{B}} [1]^^(5+n) *> [0;0;0;1;1;1]^^n *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 5 step1.
  follow' (IHn ([1;0]*>l) ([0;0;0;0;0]*>r)).
  es. er.
  follow' (Incs1 1 (6+n) n (l) ([0;0]*>r)).
  simpl_nat.
  do 7 step1.
  simpl_rotate.
  follow' (IHn ([1]*>l) ([0;0;0;1;1;1]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* <[1;0]^^(12+n) <* [0] <* [1]^^(63+n*5) <{{D}} [1;1;1] *> 0inf.
Proof.
  induction n.
  1: solve_init.
  follow IHn; clear IHn.
  remember (12+n) as n'.
  replace (12+S n) with (1+n') by lia.
  replace (63+n*5) with (3+n'*5) by lia.
  replace (63+S n*5) with (8+n'*5) by lia.
  follow' (P0_n (n') (0inf) ([1;1;1]*>0inf)).
  es; er.
  follow' (Incs2 1 (2+n') n' (0inf) ([1;1;1]*>0inf)).
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB1RA_0RC1LB_1RD0RA_0LE---_0LA0LF_1LE0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[0]^^a <* [0] <* [1]^^b <* [1] {{B}}> [1;0]^^c *> r.
Definition S2 a b c l r := l <* <[0]^^a <* [0] <* [1]^^b <* <[1;0] {{C}}> [1;0;0;0;0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (1+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (2+a) (3+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*2+a) (c*3+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Definition P0 n :=
  forall l r,
  l <* <[0]^^(5+n*3) <* [1]^^(4+n*4) <{{E}} r -->*
  l <{{F}} [0;1]^^(2+n) *> [0;0;1;0;0]^^(1+n) *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 4 step1.
  follow' (IHn ([0;0;0]*>l) ([0;0;0;0]*>r)).
  es. er.
  follow (Incs1 0 2 n).
  es. er.
  follow (Incs2 0 (5+n) n).
  unfold S2.
  cbn.
  simpl_rotate.
  rewrite Nat.add_0_r.
  rewrite lpow_add'.
  simpl_nat.
  cbn.
  do 6 step1.
  follow' (IHn ([0;1]*>l) ([0;0;1;0;0]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1] <* [0]^^(6+n*3) <* [1]^^(6+n*4) <{{E}} [1] *> 0inf.
Proof.
  induction n.
  1: solve_init.
  follow IHn; clear IHn.
  do 2 step1.
  follow' (P0_n n ([0;1]*>0inf) ([0;0;1]*>0inf)).
  es. er.
  follow (Incs1 0 3 n).
  es. er.
  follow (Incs2 0 (9+n) n).
  unfold S2.
  cbn.
  simpl_rotate.
  rewrite Nat.add_0_r.
  rewrite lpow_add'.
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1RB0RE_0LC---_0LE0LD_1LC0LC_1RF1RE_0RA1LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* <[0]^^a <* [0] <* [1]^^b <* [1] {{F}}> [1;0]^^c *> r.
Definition S2 a b c l r := l <* <[0]^^a <* [0] <* [1]^^b <* <[1;0] {{A}}> [1;0;0;0;0]^^c *> r.
Definition S3 a b c l r := l <* <[0]^^a <* [0] <* [1]^^b <* <[1;0;0;1;0] {{A}}> [0;0;1;0;0]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (1+a) (1+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c+a) (c+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (2+a) (3+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*2+a) (c*3+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (2+a) (3+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c*2+a) (c*3+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.
Definition P0 n :=
  forall l r,
  l <* <[0]^^(5+n*3) <* [1]^^(4+n*4) <{{C}} r -->*
  l <{{D}} [0;1]^^(2+n) *> [0;0;1;0;0]^^(1+n) *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 4 step1.
  follow' (IHn ([0;0;0]*>l) ([0;0;0;0]*>r)).
  es. er.
  follow (Incs1 0 2 n).
  es. er.
  follow (Incs2 0 (5+n) n).
  unfold S2.
  cbn.
  simpl_rotate.
  rewrite Nat.add_0_r.
  rewrite lpow_add'.
  simpl_nat.
  cbn.
  do 6 step1.
  follow' (IHn ([0;1]*>l) ([0;0;1;0;0]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1] <* [0]^^(6+n*3) <* [1]^^(6+n*4) <{{C}} [1;0;0;1] *> 0inf.
Proof.
  induction n.
  1: solve_init.
  follow IHn; clear IHn.
  do 2 step1.
  follow' (P0_n n ([0;1]*>0inf) ([0;0;1;0;0;1]*>0inf)).
  es. er.
  follow (Incs1 0 3 n).
  es. er.
  follow (Incs3 0 (6+n) n).
  unfold S3.
  cbn.
  simpl_rotate.
  rewrite Nat.add_0_r.
  rewrite lpow_add'.
  simpl_nat.
  cbn.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM10.

Module TM11.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC0LC_1RE1LD_0LB0RA_1RD1RF_0RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

Definition S1 a b c l r := l <* [1]^^a <* [0] <* <[0;0;1]^^b <* [0] {{A}}> [1;1;0;0;1]^^c *> r.
Definition S2 a b c l r := l <* [1]^^a <* [0] <* <[0;0;1]^^b {{D}}> [1;1;1;0;0]^^c *> r.
Definition S3 a b c l r := l <* [1]^^a <* [0] <* <[0;0;1]^^b <* [0;0] {{E}}> [1;0;0;1;1]^^c *> r.

Lemma Inc1 a b c l r:
  S1 a b (1+c) l r -->*
  S1 (2+a) (1+b) c l r.
Proof. es. Qed.

Lemma Incs1 a b c l r:
  S1 a b c l r -->*
  S1 (c*2+a) (c+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc1.
Qed.

Lemma Inc2 a b c l r:
  S2 a b (1+c) l r -->*
  S2 (2+a) (1+b) c l r.
Proof. es. Qed.

Lemma Incs2 a b c l r:
  S2 a b c l r -->*
  S2 (c*2+a) (c+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc2.
Qed.

Lemma Inc3 a b c l r:
  S3 a b (1+c) l r -->*
  S3 (2+a) (1+b) c l r.
Proof. es. Qed.

Lemma Incs3 a b c l r:
  S3 a b c l r -->*
  S3 (c*2+a) (c+b) 0 l r.
Proof.
  gen a b l r.
  ind c Inc3.
Qed.

Definition P0 n :=
  forall l r,
  l <* [1]^^(2+n*2) <* [0;0] <* [0;1;0]^^(1+n*2) <{{D}} r -->*
  l <{{C}} [1] *> [0;1;1]^^(2+n) *> [1;0;0;1;1]^^n *> r.

Lemma P0_n n: P0 n.
Proof.
  unfold P0.
  induction n.
  1: es.
  intros.
  do 14 step1.
  follow' (IHn ([1;1]*>l) ([1;0;0;1;0;0]*>r)).
  es. er.
  follow (Incs1 0 (2+n) n).
  replace (n+(2+n)) with (2+n*2) by lia.
  do 10 step1.
  follow' (IHn ([1;0;0]*>l) ([1;0;0;1;1]*>r)).
  es.
Qed.

Lemma BigStep n:
  c0 -->*
  0inf <* [1]^^(4+n*2) <* [0;0] <* [0;1;0]^^(1+n*2) <{{D}} [1] *> 0inf.
Proof.
  induction n.
  1: solve_init.
  follow IHn; clear IHn.
  mid (0inf <* [1]^^(4+n*2) <* [0;0] <* [0;1;0]^^(2+n*2) <{{D}} [1] *> 0inf).
  1:{
    follow' (P0_n n ([1;1]*>0inf) ([1]*>0inf)).
    es. er.
    follow (Incs2 0 (2+n) n).
    unfold S2.
    replace (n+(2+n)) with (2+n*2) by lia.
    do 7 step1.
    follow' (P0_n n ([1]*>0inf) ([1]*>0inf)).
    es. er.
    follow (Incs2 0 (3+n) n).
    unfold S2.
    replace (n+(3+n)) with (3+n*2) by lia.
    es.
  }
  mid (0inf <* [1]^^(4+n*2) <* [0;0] <* [0;1;0]^^(3+n*2) <{{D}} [1] *> 0inf).
  1:{
    do 7 step1.
    follow' (P0_n n ([1;1]*>0inf) ([1;0;0;1]*>0inf)).
    es. er.
    follow (Incs1 0 (2+n) n).
    unfold S1.
    replace (n+(2+n)) with (2+n*2) by lia.
    do 10 step1.
    follow' (P0_n n ([1]*>0inf) ([1;0;0;1;1]*>0inf)).
    es. er.
    follow (Incs3 0 (3+n) n).
    unfold S3.
    replace (n+(3+n)) with (3+n*2) by lia.
    es.
  }
  follow' (P0_n (1+n) (0inf) ([1]*>0inf)).
  es. er.
  follow (Incs2 0 (4+n) n).
  unfold S2.
  replace (n+(4+n)) with (4+n*2) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  solve_sigma_score' BigStep.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC0RF_0LD0LC_1RE0LE_0RB0RC_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Ltac follow' H :=
  let I1:=fresh "I" in
  epose proof H as I1;
  (eapply evstep_progress_trans || eapply evstep_trans); [| follow H]; [es | ].

Definition S1 l a b c r :=
  l <* <[1;0]^^a <* <[0;0] <* <[1]^^b {{B}}> [1;0;0;0;0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a b (1+c) r -->*
  S1 l (1+a) (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b c r -->*
  S1 l (c+a) (c*3+b) 0 r.
Proof.
  gen a b.
  ind c Inc1.
Qed.

Lemma P1 n m l r:
  l <* <[1;0]^^m <* <[0;0] <* <[1;1]^^m {{A}}> [1;0]^^(4+n*2) *> [0]^^(4+n*5) *> [0;0;0;0;1]^^m *> [0;0;0;0;0] *> r -->*
  l <{{E}} [0;0] *> [1;0]^^(4+m*2+n*2) *> [0]^^(8+m*5+n*5) *> [1] *> r.
Proof.
  gen m l r.
  induction n; intros.
  - mid (S1 (l) (3+m) (10+m*2) m ([0]*>r)).
    1: es.
    follow Incs1.
    replace (m+(3+m)) with (3+m*2) by lia.
    replace (m*3+(10+m*2)) with (10+m*5) by lia.
    es.
  - follow' (IHn O ([1;1]^^(1+m)*>[0;0]*>[0;1]^^m*>l) ([0;0;0;0;1]^^m*>[0;0;0;0;0]*>r)).
    epose proof (IHn (1+m) l r) as I1.
    remember (4+0*2+n*2) as v1.
    do 2 (er; sr).
    subst.
    follow' I1.
    es.
Qed.

Definition S0 '(n,m) := 0inf <* <[1;0]^^(1+m) <* <[0;0] <* <[1;1]^^m {{A}}> [1;0]^^(4+n*2) *> [0]^^(4+n*5) *> [0;0;0;0;1]^^m *> [0;0;1] *> 0inf.

Lemma BigStep_1 n m:
  S0 (1+n,m) -->+ S0 (n,1+m).
Proof.
  unfold S0.
  follow' (P1 n 0 (0inf<*<[1;0]^^(1+m)<*<[0;0]<*<[1;1]^^(1+m)) ([0;0;0;0;1]^^m*>[0;0;1]*>0inf)).
  remember (4+0*2+n*2) as v1.
  do 2 (er; sr).
  subst.
  es.
Qed.

Definition S2 a b c :=
  [1;0;0] *> [1]^^b *> [0;0;0] *> [1;0]^^a *> 0inf
  {{B}}> [0;0;1;0;0]^^c *> [1] *> 0inf.

Lemma Inc2 a b c:
  S2 a b (1+c) -->*
  S2 (1+a) (3+b) c.
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 (c+a) (c*3+b) 0.
Proof.
  gen a b.
  ind c Inc2.
Qed.

Lemma BigStep_0 m:
  S0 (O,m) -->+ S0 (1+m,O).
Proof.
  mid10 (S2 (3+m) (7+m*2) m).
  1: es.
  follow Incs2.
  replace (m+(3+m)) with (3+m*2) by lia.
  replace (m*3+(7+m*2)) with (7+m*5) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros [n m].
  destruct n.
  - eexists; apply BigStep_0.
  - eexists; apply BigStep_1.
Qed.

End TM12.


Module TM13.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RB_1LD0RE_0LA0LD_0RF---_1RC1RF").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Ltac follow' H :=
  let I1:=fresh "I" in
  epose proof H as I1;
  (eapply evstep_progress_trans || eapply evstep_trans); [| follow H]; [es | ].

Definition S1 l a b c r :=
  l <* <[1;0]^^a <* <[0;0] <* <[1]^^b {{C}}> [1;0;0;0;0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a b (1+c) r -->*
  S1 l (1+a) (3+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b c r -->*
  S1 l (c+a) (c*3+b) 0 r.
Proof.
  gen a b.
  ind c Inc1.
Qed.

Lemma P1 n m l r:
  l <* <[1;0]^^m <* <[0;0] <* <[1;1]^^m {{F}}> [1;0]^^(4+n*2) *> [0]^^(4+n*5) *> [0;0;0;0;1]^^m *> [0;0;0;0;0] *> r -->*
  l <{{B}} [0;0] *> [1;0]^^(4+m*2+n*2) *> [0]^^(8+m*5+n*5) *> [1] *> r.
Proof.
  gen m l r.
  induction n; intros.
  - mid (S1 (l) (3+m) (10+m*2) m ([0]*>r)).
    1: es.
    follow Incs1.
    replace (m+(3+m)) with (3+m*2) by lia.
    replace (m*3+(10+m*2)) with (10+m*5) by lia.
    es.
  - follow' (IHn O ([1;1]^^(1+m)*>[0;0]*>[0;1]^^m*>l) ([0;0;0;0;1]^^m*>[0;0;0;0;0]*>r)).
    epose proof (IHn (1+m) l r) as I1.
    remember (4+0*2+n*2) as v1.
    do 2 (er; sr).
    subst.
    follow' I1.
    es.
Qed.

Definition S0 '(n,m) := 0inf <* <[1;0]^^(1+m) <* <[0;0] <* <[1;1]^^m {{F}}> [1;0]^^(4+n*2) *> [0]^^(4+n*5) *> [0;0;0;0;1]^^m *> [0;1] *> 0inf.

Lemma BigStep_1 n m:
  S0 (1+n,m) -->+ S0 (n,1+m).
Proof.
  unfold S0.
  follow' (P1 n 0 (0inf<*<[1;0]^^(1+m)<*<[0;0]<*<[1;1]^^(1+m)) ([0;0;0;0;1]^^m*>[0;1]*>0inf)).
  remember (4+0*2+n*2) as v1.
  do 2 (er; sr).
  subst.
  es.
Qed.

Definition S2 a b c :=
  [0;0] *> [1]^^b *> [0;0;0] *> [1;0]^^a *> 0inf
  {{F}}> [0;0;0;1;0]^^c *> [1] *> 0inf.

Lemma Inc2 a b c:
  S2 a b (1+c) -->*
  S2 (1+a) (3+b) c.
Proof.
  es.
Qed.

Lemma Incs2 a b c:
  S2 a b c -->*
  S2 (c+a) (c*3+b) 0.
Proof.
  gen a b.
  ind c Inc2.
Qed.

Lemma BigStep_0 m:
  S0 (O,m) -->+ S0 (1+m,O).
Proof.
  mid10 (S2 (3+m) (7+m*2) m).
  1: es.
  follow Incs2.
  replace (m+(3+m)) with (3+m*2) by lia.
  replace (m*3+(7+m*2)) with (7+m*5) by lia.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: unfold S0; esx.
  eapply progress_nonhalt_simple.
  intros [n m].
  destruct n.
  - eexists; apply BigStep_0.
  - eexists; apply BigStep_1.
Qed.

End TM13.


Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0RF_1RD0LC_0LE1LD_0RA1LC_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Ltac follow' H :=
  let I1:=fresh "I" in
  epose proof H as I1;
  (eapply evstep_progress_trans || eapply evstep_trans); [| follow H]; [es | ].

Definition S1 l a b c r :=
  l <* <[0;1]^^a <* <[0;0] <* <[1]^^b {{B}}> [0;0;1;0]^^c *> r.

Lemma Inc1 l a b c r:
  S1 l a b (1+c) r -->*
  S1 l (1+a) (2+b) c r.
Proof.
  es.
Qed.

Lemma Incs1 l a b c r:
  S1 l a b c r -->*
  S1 l (c+a) (c*2+b) 0 r.
Proof.
  gen a b.
  ind c Inc1.
Qed.

Lemma P1 n m l r:
  l <* <[0;1]^^m <* <[0;0] <* <[1]^^(2+m) {{B}}> [1;1;1;0]^^(1+n) *> [0]^^(3+n*3) *> [0;0;1;0]^^m *> r -->*
  l <* <[0;1]^^(2+m*2+n*2) <* <[0;0] <* <[1]^^(5+m*3+n*3) {{B}}> r.
Proof.
  gen m l r.
  induction n; intros.
  - mid (S1 (l) (2+m) (5+m) m r).
    1: es.
    follow Incs1.
    replace (m+(2+m)) with (2+m*2) by lia.
    replace (m*2+(5+m)) with (5+m*3) by lia.
    es.
  - follow' (IHn O ([1]^^(2+m)*>[0;0]*>[1;0]^^m*>l) ([0;0;0]*>[0;0;1;0]^^m*>r)).
    follow' (IHn (1+m) l r).
    finish.
Qed.

Definition S' n :=
  0inf <* <[1] <* <[0;0;1;1] {{B}}> [1;1;1;0]^^(1+n) *> [0]^^(3+n*3) *> 0inf.

Lemma BigStep n:
  S' n -->+
  S' (1+n).
Proof.
  follow (P1 n 0 (0inf<*<[1]) 0inf).
  follow' (P1 n O (0inf<*<[1]) ([0;0;1]*>0inf)).
  follow' (P1 n 0 (0inf<*<[1;0;0;1]) ([0;0;0;0;1]*>0inf)).
  follow' (P1 n O (0inf<*<[1;0;1]) ([0;0;1]^^2*>0inf)).
  unfold S'.
  rewrite (lpow_all0 [0]) by solve_const0_eq.
  st.
  er; sr.
  er; sr.
  er; use_shift_rule.
  rewrite (lpow_all0 [0;0;0]) by solve_const0_eq.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' 0).
  1: unfold S'; esx.
  eapply progress_nonhalt_simple.
  intros n; eexists; apply BigStep.
Qed.

End TM15.


