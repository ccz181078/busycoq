From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.


Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
  execute_with_shift_rule.


Ltac step1s_follow H :=
  (follow H || (step1; step1s_follow H)).


Section FractalType5v3.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QR QL QR2:Q.
Hypothesis a0 a1:nat.

Notation "l |> r" :=
  (l <* [1] {{QR}}> r) (at level 30).

Definition P1 i n n0 :=
  forall l r,
    l <* [1;1]^^i |> [0] *> [0;0]^^n0 *> r -->*
    l <{{QL}} [0;1]^^n *> r.

Definition P1' i n n0 :=
  forall l r,
    l <* [1;1]^^i |> [1] *> [1;0]^^n0 *> r -->*
    l <{{QL}} [0;1]^^n *> r.

Definition P3 i n n0 :=
  forall l r,
    l {{QR2}}> [0] *> [1;0]^^n *> r -->*
    l <* [1;0]^^n0 <* [0] <* [1;1]^^i |> [1] *> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [0] <* [1;1]^^i |> [0;0]^^n1 *> r -->+
    l <* [1;0]^^n0 <* [0;1;0] <* [1;1]^^(1+i) |> r.


Hypothesis nxtP1:
  forall i n n1,
    P1 i n n1 ->
    P3 i n n1 ->
    P1 (i+1) (2+n1+n) (1+n1+n1).

Hypothesis nxtP1':
  forall i n n1,
    P1' i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1' (i+1) (3+n1+n) (2+n1+n1).

Hypothesis nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P1' i (1+n) (1+n1) ->
    P3 (i+1) (2+n1+n) (1+n1+n1).

Hypothesis nxtP4:
  forall i n n1,
    P1 i n n1 ->
    P3 i n n1 ->
    P4 i n1 (n1+2).


Fixpoint Ns i :=
match i with
| O => (5,3)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,1+n1+n1)
end.


Hypothesis Pi_O:
  let (n,n1):=Ns O in
  P1 1 n n1 /\
  P1' 1 (1+n) (1+n1) /\
  P3 1 n n1.


Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P1 (S i) n n1 /\
  P1' (S i) (1+n) (1+n1) /\
  P3 (S i) n n1.
Proof.
  induction i.
  - apply Pi_O.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S (S i)) with ((S i)+1) by lia.
    repeat split.
    + apply nxtP1; tauto.
    + apply nxtP1'; tauto.
    + apply nxtP3; tauto.
Qed.

Definition config (x:nat*side) :=
  let (n,l):=x in
  l <* [0] <* [1;1]^^(S n) |> const 0.


Hypothesis init:
  c0 -->* config (a0%nat,const 0 <* [1;0]^^a1).

Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (a0%nat,const 0 <* [1;0]^^a1)).
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i l].
  unfold config.
  pose proof (Pi_spec i) as H.
  destruct (Ns i) as [n n1].
  destruct H as [HP1 [HP1' HP3]].
  pose proof (nxtP4 _ _ _ HP1 HP3) as H.
  eexists (S i,_).
  unfold P4 in H.
  specialize (H l (const 0)).
  rewrite lpow_all0 in H. 2: solve_const0_eq.
  follow10 H.
  finish.
Qed.

End FractalType5v3.



Inductive Cert :=
| cert1(QR QL QR2:Q)(a0 a1:nat)
.

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QR ?QL ?QR2 ?a0 ?a1) =>
  eapply (nonhalt _
    QR QL QR2 a0 a1);
  [ try (intros i n n1;
    unfold P1,P3;
    intros HP1 HP3 l r;
    replace (1+n1+n1) with (n1+(1+n1)) by lia;
    repeat rewrite lpow_add,Str_app_assoc;
    follow HP1;
    cbn; simpl_rotate;
    step1s_follow HP3;
    step1;
    rewrite <-lpow_shift21;
    follow HP1;
    es; fail)
  | try (intros i n n1;
    unfold P1',P3;
    intros HP1' HP3 l r;
    replace (2+n1+n1) with ((1+n1)+(1+n1)) by lia;
    do 2 rewrite lpow_add,Str_app_assoc;
    follow HP1';
    cbn;
    rewrite <-lpow_shift21;
    step1s_follow HP3;
    step1;
    rewrite <-lpow_shift21;
    follow HP1';
    es; fail)
  | try (intros i n n1;
    unfold P3,P1';
    intros HP3 HP1' l r;
    replace (2+n1+n) with (n+(n1+2)) by lia;
    rewrite lpow_add,Str_app_assoc;
    follow HP3;
    replace (n1+2) with (1+n1+1) by lia;
    rewrite lpow_add,Str_app_assoc;
    follow HP1';
    er; sr; er; sr;
    rewrite <-lpow_shift21;
    step1s_follow HP3;
    er; fail)
  | try (intros i n n1;
    unfold P1,P3,P4;
    intros HP1 HP3 l r;
    rewrite lpow_add,Str_app_assoc;
    cbn;
    rewrite lpow_rotate; cbn;
    follow HP1;
    er; sr; er; sr;
    rewrite <-lpow_shift21;
    step1s_follow HP3;
    er; fail)
  | try (intros; cbn; unfold P1,P1',P3,P4; repeat split; es; fail)
  | try (intros; unfold config; cbn; solve_init; fail)
  ]
end.


Definition tm1 := Eval compute in (TM_from_str "1RB1RF_0RC0RA_1LD1RC_0LE0LE_1RA0LB_1LE---").
Lemma nonhalt1:~halts tm1 c0.
Proof.
  solve_cert (cert1 C E B 0 2).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB0RF_0RC0RA_1LD1RC_0LE0LE_1RA0LB_1LC---").
Lemma nonhalt2:~halts tm2 c0.
Proof.
  solve_cert (cert1 C E B 0 2).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB0LC_1RC1RF_0RD0RB_1LE1RD_0LA0LA_1LA---").
Lemma nonhalt3:~halts tm3 c0.
Proof.
  solve_cert (cert1 D A C 1 4).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1RB0LC_1RC0RF_0RD0RB_1LE1RD_0LA0LA_1LD---").
Lemma nonhalt4:~halts tm4 c0.
Proof.
  solve_cert (cert1 D A C 1 4).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1LB1RA_0LC0LC_1RD0LE_1RE1RF_0RA0RD_1LC---").
Lemma nonhalt5:~halts tm5 c0.
Proof.
  solve_cert (cert1 A C E 2 8).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB1RA_0LC0LC_1RD0LE_1RE0RF_0RA0RD_1LA---").
Lemma nonhalt6:~halts tm6 c0.
Proof.
  solve_cert (cert1 A C E 2 8).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1RB0RF_0RC0RA_1LD1RC_0LE0RE_1RA0LB_1LC---").
Lemma nonhalt7:~halts tm7 c0.
Proof.
  solve_cert (cert1 C E B 0 2).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1RB0LC_1RC0RF_0RD0RB_1LE1RD_0LA0RA_1LD---").
Lemma nonhalt8:~halts tm8 c0.
Proof.
  solve_cert (cert1 D A C 1 4).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB1RF_0RC0RA_1LD1RC_0LE0RE_1RA0LB_1LE---").
Lemma nonhalt9:~halts tm9 c0.
Proof.
  solve_cert (cert1 C E B 0 2).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1RB0LC_1RC1RF_0RD0RB_1LE1RD_0LA0RA_1LA---").
Lemma nonhalt10:~halts tm10 c0.
Proof.
  solve_cert (cert1 D A C 1 4).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1LB1RA_0LC0RC_1RD0LE_1RE1RF_0RA0RD_1LC---").
Lemma nonhalt11:~halts tm11 c0.
Proof.
  solve_cert (cert1 A C E 2 8).
Qed.


Definition tm12 := Eval compute in (TM_from_str "1LB1RA_0LC0RC_1RD0LE_1RE0RF_0RA0RD_1LA---").
Lemma nonhalt12:~halts tm12 c0.
Proof.
  solve_cert (cert1 A C E 2 8).
Qed.


