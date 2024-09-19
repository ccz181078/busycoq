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


Section FractalType5v2.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QR QL1 QL2:Q.
Hypothesis qR qL1 qL2 initL:list sym.


Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [1] *> [0]^^n0 *> r -->*
    l <{{QL1}} qL1 *> [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [0;0]^^i |> [0] *> [0]^^n0 *> r -->*
    l <{{QL2}} qL2 *> [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* [1;1] |> [0]^^n *> r -->*
    l <* [1]^^n0 <* [1] <* [0;0]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* [1] <* [0;0]^^i |> [0]^^(1+n1) *> r -->+
    l <* [1]^^n0 <* [1] <* [0;0]^^(1+i) |> r.


Hypothesis nxtP0:
  forall i n n1,
    P0 i (1+n) n1 ->
    P3 i n n1 ->
    P0 (i+1) (3+n1+n) (n1+n1).

Hypothesis nxtP1:
  forall i n n1,
    P0 i (1+n) n1 ->
    P1 i (1+n) (1+n1) ->
    P3 i n n1 ->
    P1 (i+1) (3+n1+n) (1+n1+n1).

Hypothesis nxtP3:
  forall i n n1,
    P3 i n n1 ->
    P4 i n1 (n1+1) ->
    P3 (i+1) (2+n1+n) (n1+n1).

Hypothesis nxtP4:
  forall i n n1,
    P1 i (n+1) (n1+1) ->
    P3 i n n1 ->
    P4 i n1 (n1+1).

Fixpoint Ns i :=
match i with
| O => (0,1)%nat
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Hypothesis Pi_O:
  let (n,n1):=Ns O in
  P0 O (1+n) n1 /\
  P1 O (1+n) (1+n1) /\
  P3 O n n1 /\
  P4 O n1 (n1+1).


Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 i (1+n) n1 /\
  P1 i (1+n) (1+n1) /\
  P3 i n n1 /\
  P4 i n1 (n1+1).
Proof.
  induction i.
  - apply Pi_O.
  - cbn.
    destruct (Ns i) as [n n1].
    replace (S i) with (i+1) by lia.
    destruct IHi as [HP0 [HP1 [HP3 HP4]]].
    pose proof (nxtP0 _ _ _ HP0 HP3) as HP0'.
    pose proof (nxtP1 _ _ _ HP0 HP1 HP3) as HP1'.
    pose proof (nxtP3 _ _ _ HP3 HP4) as HP3'.
    repeat split; try assumption.
    eapply nxtP4 with (n:=2+n1+n).
    + applys_eq HP1'; lia.
    + applys_eq HP3'; lia.
Qed.


Definition config (x:nat*side) :=
  let (n,l):=x in
  l <* [1] <* [0;0]^^n |> const 0.

Hypothesis init:
  c0 -->* config (0%nat,const 0 <* initL).


Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config (0%nat,const 0 <* initL)).
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  destruct i as [i l].
  unfold config.
  pose proof (Pi_spec i) as H.
  destruct (Ns i) as [n n1].
  eexists (S i,_).
  destruct H as [_ [_ [_ H]]].
  unfold P4 in H.
  specialize (H l (const 0)).
  rewrite lpow_all0 in H. 2: solve_const0_eq.
  follow10 H.
  finish.
Qed.

End FractalType5v2.



Inductive Cert :=
| cert1(QR QL1 QL2:Q)(qR qL1 qL2 initL:list sym)
.

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QR ?QL1 ?QL2 ?qR ?qL1 ?qL2 ?initL) =>
  eapply (nonhalt _
    QR QL1 QL2 qR qL1 qL2 initL);
  [ try (intros i n n1;
    unfold P0,P3;
    intros HP0 HP3 l r;
    repeat rewrite lpow_add,Str_app_assoc;
    follow HP0;
    step1s_follow HP3;
    follow HP0;
    es; fail)
  | try (intros i n n1;
    unfold P0,P1,P3;
    intros HP0 HP1 HP3 l r;
    repeat rewrite lpow_add,Str_app_assoc;
    follow HP1;
    step1s_follow HP3;
    follow HP0;
    es; fail)
  | try (intros i n n1;
    unfold P3,P4;
    intros HP3 HP4 l r;
    rewrite (Nat.add_comm _ n);
    rewrite lpow_add,Str_app_assoc;
    step1s_follow HP3;
    replace (2+n1) with (1+(n1+1)) by lia;
    follow100 HP4;
    es; fail)
  | try (intros i n n1;
    unfold P1,P3,P4;
    intros HP1 HP3 l r;
    rewrite lpow_add,Str_app_assoc;
    follow HP1;
    repeat rewrite lpow_add,Str_app_assoc;
    step1s_follow HP3;
    es; fail)
  | try (intros; cbn; unfold P0,P1,P3,P4; repeat split; es; fail)
  | try (intros; unfold config; cbn; solve_init; fail)
  ]
end.


Definition tm1 := Eval compute in (TM_from_str "1LB---_1LC0LB_1RC1RD_1RE1RE_0RF1RA_1RA0RE").
Lemma nonhalt1:~halts tm1 c0.
Proof.
  solve_cert (cert1 E B C [] [] [1] [1;1]).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB1RB_0RC1RD_1RD0RB_1LE---_1LF0LE_1RF1RA").
Lemma nonhalt2:~halts tm2 c0.
Proof.
  solve_cert (cert1 B E F [] [] [1] []).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1LB1RC_1RB1RA_0RD1RE_1RE0RC_1LF---_1LB0LF").
Lemma nonhalt3:~halts tm3 c0.
Proof.
  solve_cert (cert1 C F B [] [] [1] [1;1]).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB0LA_1RB1RC_1RD0LB_0RE1RF_1RF0RD_1LA---").
Lemma nonhalt4:~halts tm4 c0.
Proof.
  solve_cert (cert1 D A B [] [] [1] [1;1]).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB0LF_0RC1RD_1RD0RB_1LE---_1LF0LE_1RF1RA").
Lemma nonhalt5:~halts tm5 c0.
Proof.
  solve_cert (cert1 B E F [] [] [1] []).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB0LA_1RC1RF_0RD1RB_0RE---_0RF1LA_1LA0LC").
Lemma nonhalt6:~halts tm6 c0.
Proof.
  solve_cert (cert1 E A B [0;0] [0;0] [1;0;0] [1;1]).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1RB1RE_0RC1RA_0RD---_0RE1LF_1LF0LB_1LA0LF").
Lemma nonhalt7:~halts tm7 c0.
Proof.
  solve_cert (cert1 D F A [0;0] [0;0] [1;0;0] []).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB0LA_1RC1RF_0RD1RB_0RE---_0RF0LE_1LA0LC").
Lemma nonhalt8:~halts tm8 c0.
Proof.
  solve_cert (cert1 E A B [0;0] [0;0] [1;0;0] [1;1]).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB1RE_0RC1RA_0RD---_0RE0LD_1LF0LB_1LA0LF").
Lemma nonhalt9:~halts tm9 c0.
Proof.
  solve_cert (cert1 D F A [0;0] [0;0] [1;0;0] []).
Qed.


