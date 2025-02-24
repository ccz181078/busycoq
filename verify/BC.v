From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import SimplTape.

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

Definition tm := Eval compute in (TM_from_str "1LB0LA_0RC0LA_1RD1RB_1RE1RD_1LF1LE_---0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{C}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{D}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{D}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (2,O)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_---0LD_0RE0LF_1RA1RD_1LD0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{E}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{A}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{A}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (O,O)).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1RB_1LD1LC_---0LE_0RA0LF_1LE0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* <[1;0]^^n {{A}}> [0]^^(3+m*2) *> r -->*
  const 0 <* <[1;0]^^(k1+n) <* [1]^^k2 {{B}}> r.

Lemma P0_S m k1:
  P0 m k1 (3+m*2) ->
  P0 (S m) (1+k1+k1) (2+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (3+m*2) ->
  P0 (2+m) (1+3*k1') (3+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (1+n*2) k1 (3+(1+n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 1%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* <[1;0]^^n <* [1]^^(3+(1+m*2)*2) {{B}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1LB_0LD0LC_0RE0RA_1RE1LF_---1LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P0 m k1 k2 :=
  forall n r,
  const 0 <* [1]^^(1+n) {{A}}> [0]^^(2+m*2) *> r -->*
  const 0 <* [1]^^(1+k1+n) <* [0] <* [1]^^k2 {{A}}> r.

Lemma P0_S m k1:
  P0 m k1 (2+m*2) ->
  P0 (S m) (1+k1+k1) (1+(S m)*2).
Proof.
  unfold P0.
  intros HP0 n r.
  follow' (HP0 n ([0;0]*>r)).
  remember (k1+n) as n0.
  do 3 (er; sr).
  follow' (HP0 (1+n0) ([1]*>r)).
  subst.
  es.
Qed.

Lemma P0_S' m k1':
  P0 (m) k1' (2+m*2) ->
  P0 (2+m) (1+3*k1') (2+(2+m)*2).
Proof.
  unfold P0.
  intros HP0' n r.
  pose proof (P0_S _ _ HP0') as HP0''.
  unfold P0 in HP0''.
  follow' (HP0'' n ([0;0]*>r)).
  remember (k1'+k1'+n) as n0'.
  do 3 (er; sr).
  follow' (HP0' (2+n0') ([0;1]*>r)).
  subst.
  es.
Qed.

Lemma P0_n n:
  exists k1,
  P0 (n*2) k1 (2+(n*2)*2).
Proof.
  induction n.
  1: unfold P0; exists 0%nat; es.
  destruct IHn as [k1 IHn].
  pose proof (P0_S' _ _ IHn).
  eexists.
  applys_eq H.
Qed.

Definition S0 '(n,m) :=
  const 0 <* [1]^^(1+n) <* [0] <* [1]^^(2+(m*2)*2) {{A}}> const 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S0 (1,0)%nat).
  1: unfold S0; cbn; solve_init.
  eapply progress_nonhalt_simple.
  intros [n m].
  pose proof (P0_n m) as [k1 HP0].
  pose proof (P0_S _ _ HP0) as HP0'.
  unfold P0 in *.
  eexists (1+k1+k1+n,1+m).
  unfold S0.
  do 3 (er; sr).
  follow' (HP0 (1+n) ([1]*>0inf)).
  remember (k1+S n) as n'.
  do 3 (er; sr).
  follow' (HP0 (1+n') ([0;1]*>0inf)).
  subst.
  es.
Qed.

End TM4.

