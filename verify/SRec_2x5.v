From BusyCoq Require Import Individual25.
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


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB2RB4LB0LB---_1LA3RB4RA0LA1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition P1 n :=
  forall l r,
  l <* [1] {{B}}> [0;0]^^n *> r -->*
  l <* [4]^^n <* [1] <* [3]^^n {{B}}> r.

Definition P3 n :=
  forall l r,
  l <* [4]^^n <* [1] <* [3]^^n <{{A}} r -->*
  l <* [2] <* [3;3]^^n {{B}}> r.

Definition P4 n :=
  forall l r,
  l <* [4]^^n <* [1] <* [3]^^(1+n) <{{A}} r -->*
  l <{{B}} [0;1] *> [1;1]^^n *> r.

Lemma P1_S n:
  P1 n ->
  P3 n ->
  P1 (1+n).
Proof.
  unfold P1,P3.
  intros HP1 HP3 l r.
  follow' (HP1 l ([0;0]*>r)).
  step1.
  follow' (HP3 l ([1;0]*>r)).
  er; sr.
  do 2 step1.
  follow' (HP1 (l<*[4]) ([1]*>r)).
  er.
Qed.

Lemma P3_S n:
  P1 n ->
  P3 n ->
  P4 n ->
  P3 (2+n).
Proof.
  unfold P1,P3,P4.
  intros HP1 HP3 HP4 l r.
  do 2 step1.
  follow' (HP3 (l<*[4;4]) ([0;0]*>r)).
  er; sr.
  do 3 step1.
  follow' (HP1 ([1;4]*>l) ([1;0]*>r)).
  do 2 step1.
  follow' (HP4 ([1;4]*>l) ([1]*>r)).
  es.
Qed.

Lemma P4_S n:
  P1 (1+n) ->
  P4 n ->
  P4 (1+n) ->
  P4 (2+n).
Proof.
  unfold P1,P4.
  intros HP1 HP4 HP4' l r.
  do 2 step1.
  follow' (HP4 (l<*[4;4]) ([0;0]*>r)).
  er; sr.
  er; sr.
  do 3 step1.
  follow' (HP1 ([1]*>l) ([1;0]*>r)).
  do 2 step1.
  follow' (HP4' ([1]*>l) ([1]*>r)).
  es.
Qed.

Lemma P_n n:
  P1 n /\ P3 n /\ P4 n.
Proof.
  induction n using strong_induction.
  destruct n as [|[|]].
  1,2: repeat split; unfolds; es.
  epose proof (H n _) as [HP1 [HP3 HP4]].
  epose proof (H (S n) _) as [HP1' [HP3' HP4']].
  repeat split.
  - apply P1_S; tauto.
  - apply P3_S; tauto.
  - apply P4_S; tauto.
  Unshelve. all: lia.
Qed.
 
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  pose proof (P_n n) as [HP1 _].
  specialize (HP1 0inf 0inf).
  rewrite lpow_all0 in HP1.
  2: solve_const0_eq.
  eexists _,_.
  split.
  - step1.
    apply HP1.
  - split.
    1: solve_sigma_score.
    lia.
Qed.

End TM1.


