From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.
From BusyCoq Require Import NatMod.

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

Definition tm := Eval compute in (TM_from_str "1RB1RB_1RC---_1RD1RA_1LE1LF_1RF0LD_1RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{A}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{A}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{A}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{C}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1RC---_1RD1RA_1LE1LF_1RF0LD_1RA0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{A}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{A}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{A}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{C}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1LA1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{E}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{E}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{E}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 3).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1RF0LA_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{E}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{E}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{E}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 3).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1LD_1RD0LB_1RE0RC_1RF1RF_1RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{E}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{E}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{E}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{A}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 3).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1LC_1RC0LA_1RD0RB_1LE1RF_1RA1RD_1RE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{D}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{D}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{D}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{E}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 2).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1LE_1RE0LC_1RF0RD_1LB1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{F}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{F}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{F}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{B}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 5).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1LE_1RE0LC_1RF0RD_1RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{F}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{F}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{F}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{B}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 5).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1RB0LF_1RC0RA_1RD1RD_1RE---_1RF1RC_1LA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{C}}> [1;0;0]^^(m*2) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(m*2) <* [1;1] {{C}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^2*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^n-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{C}}> [1;0;0]^^(n*2) *> [1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{E}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 5).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  eexists ((2^n-1+1)+n+2).
  unfold S0.
  follow (P0_n n).
  do 2 (er; sr).
  mid (S1 (2^n-1+1) (n*2+3)).
  1: es.
  follow Incs1.
  unfold S1.
  remember ((2^n-1+1)*2+(n*2+3)) as v1.
  do 3 (er; sr).
  subst.
  es.
Qed.

End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA0RF_1RD---_1RE0RA_1LF1LB_1RB0LE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k :=
  forall n r,
  0inf <* <[1;0]^^n <* [1]^^2 {{A}}> [1;0;0]^^(2+m*3) *> r -->*
  0inf <* <[1;0]^^(k+n) <* [1;1;1]^^(2+m*3) <* <[1;0] {{A}}> r.

Lemma P0_S m k:
  P0 m k ->
  P0 (1+m) (1+k+k).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([1;0;0]^^3*>r)).
  remember (k+n) as n0.
  do 3 (er; sr).
  do 1 step1.
  follow' (HP0 (2+n0) ([1;0;0;1;0;0;0]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  P0 n (2^(1+n)-1).
Proof.
  induction n.
  1: unfold P0; es.
  applys_eq (P0_S _ _ IHn).
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Definition S0 n :=
  0inf <* <[1;0]^^2 <* [1]^^2 {{A}}> [1;0;0]^^(2+(1+n*2)*3) *> [1;0;0;1] *> 0inf.

Definition S1 a b :=
  0inf <* <[1;0]^^a <* [1;1;1]^^b <* [1] {{D}}> 0inf.

Lemma Inc1 a b:
  S1 (1+a) b -->*
  S1 a (2+b).
Proof.
  es.
Qed.

Lemma Incs1 a b:
  S1 a b -->*
  S1 0 (a*2+b).
Proof.
  gen b.
  ind a Inc1.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 0).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros n.
  remember (1+n*2) as n'.
  remember ((2^(1+n')-1+1)*2+(n'*3+6)) as v1.
  remember (v1/6) as v2.
  eexists v2.
  unfold S0.
  rewrite <-Heqn'.
  follow (P0_n n').
  do 2 (er; sr).
  mid (S1 (2^(1+n')-1+1) (n'*3+6)).
  1: es.
  follow Incs1.
  unfold S1.
  rewrite <-Heqv1.
  do 3 (er; sr).
  do 7 step1.
  fold_tape.
  assert (v1=6*v2+5). {
    subst v2.
    applys_eq Nat.Div0.div_mod.
    f_equal.
    subst v1 n'.
    replace ((1+n*2)*3) with (3+n*6) by lia.
    rw_mod.
    reflexivity.
  }
  finish.
  Unshelve.
  all: cbn; pose proof (Nat.pow_nonzero 2 (n*2)); lia.
Qed.

End TM10.

