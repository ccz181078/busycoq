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


Section FractalType5v1.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Hypothesis QR QL1 QL2 QR2:Q.
Hypothesis qR qR2:list sym.
Hypothesis a0 a1:nat.

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition P0 i n n0 :=
  forall l r,
    l <* [1;1]^^i |> [1] *> [0]^^n0 *> r -->*
    l <{{QL1}} [0]^^n *> [1] *> r.

Definition P1 i n n0 :=
  forall l r,
    l <* [1;1]^^i |> [0] *> [0]^^n0 *> r -->*
    l <{{QL2}} [0]^^n *> [1] *> r.

Definition P3 i n n0 :=
  forall l r,
    l <* qR2 {{QR2}}> [0]^^n *> r -->*
    l <* [0]^^n0 <* qR2 <* [1;1]^^i |> r.

Definition P4 i n0 n1 :=
  forall l r,
    l <* qR2 <* [1;1]^^i |> [0]^^(1+n1) *> r -->+
    l <* [0]^^n0 <* qR2 <* [1;1]^^(1+i) |> r.


Hypothesis nxtP0:
  forall i n n1,
    P0 i n n1 ->
    P3 i n n1 ->
    P0 (i+1) (2+n1+n) (n1+n1).

Hypothesis nxtP1:
  forall i n n1,
    P0 i n n1 ->
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
| O => (a0,a1)
| S i0 =>
  let (n,n1):=Ns i0 in
  (2+n1+n,n1+n1)
end.

Hypothesis Pi_O:
  let (n,n1):=Ns O in
  P0 O n n1 /\
  P1 O (1+n) (1+n1) /\
  P3 O n n1 /\
  P4 O n1 (n1+1).


Lemma Pi_spec i:
  let (n,n1):=Ns i in
  P0 i n n1 /\
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

Definition config n := const 0 <* qR2 <* [1;1]^^n |> const 0.

Hypothesis init:
  c0 -->* config 0.

Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 0).
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i.
  exists (S i).
  unfold config.
  pose proof (Pi_spec i) as H.
  destruct (Ns i) as [n n1].
  destruct H as [_ [_ [_ H]]].
  unfold P4 in H.
  specialize (H (const 0) (const 0)).
  rewrite lpow_all0 in H. 2: solve_const0_eq.
  rewrite lpow_all0 in H. 2: solve_const0_eq.
  apply H.
Qed.
End FractalType5v1.


Inductive Cert :=
| cert1(QR QL1 QL2 QR2:Q)(qR qR2:list sym)(a0 a1:nat)
.

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QR ?QL1 ?QL2 ?QR2 ?qR ?qR2 ?a0 ?a1) =>
  eapply (nonhalt _
    QR QL1 QL2 QR2 qR qR2 a0 a1);
  [ try (intros i n n1;
    unfold P0,P3;
    intros HP0 HP3 l r;
    repeat rewrite lpow_add,Str_app_assoc;
    follow HP0;
    er;
    follow HP3;
    follow HP0;
    es; fail)
  | try (intros i n n1;
    unfold P0,P1,P3;
    intros HP0 HP1 HP3 l r;
    repeat rewrite lpow_add,Str_app_assoc;
    follow HP1;
    er;
    follow HP3;
    follow HP0;
    es; fail)
  | try (intros i n n1;
    unfold P3,P4;
    intros HP3 HP4 l r;
    rewrite (Nat.add_comm _ n);
    rewrite lpow_add,Str_app_assoc;
    follow HP3;
    replace (2+n1) with (1+(n1+1)) by lia;
    follow100 HP4;
    es; fail)
  | try (intros i n n1;
    unfold P1,P3,P4;
    intros HP1 HP3 l r;
    rewrite lpow_add,Str_app_assoc;
    follow HP1;
    repeat rewrite lpow_add,Str_app_assoc;
    repeat (step1; try (follow HP3; er; fail));
    fail
    )
  | try (intros; cbn; unfold P0,P1,P3,P4; repeat split; es; fail)
  | try (intros; unfold config; cbn; solve_init; fail)
  ]
end.


Definition tm1 := Eval compute in (TM_from_str "1RB1RF_1LC---_0LC0LD_0RE0RD_0RA0RB_1RA1RB").
Lemma nonhalt1:~halts tm1 c0.
Proof.
  solve_cert (cert1 F C D E [1] [0] 3 2).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB1RC_1RC1RA_1LD---_0RA0LE_0LE0LF_0RD0RF").
Lemma nonhalt2:~halts tm2 c0.
Proof.
  solve_cert (cert1 A E F D [] [0] 1 1).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1RB0RC_0RC1RA_1LD---_0LD0LE_0RF0RE_0RA---").
Lemma nonhalt3:~halts tm3 c0.
Proof.
  solve_cert (cert1 A D E F [] [0] 1 1).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1RB0RD_1LC1RA_0RA1RA_1LE---_0LE0LF_0RC0RF").
Lemma nonhalt4:~halts tm4 c0.
Proof.
  solve_cert (cert1 A E F C [] [0] 1 1).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1RC_1LB1RA_1LD---_0RA0LE_0LE0LF_0RD0RF").
Lemma nonhalt5:~halts tm5 c0.
Proof.
  solve_cert (cert1 A E F D [] [0] 1 1).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1RB0RC_1LB1RA_1LD---_0LD0LE_0RF0RE_0RA---").
Lemma nonhalt6:~halts tm6 c0.
Proof.
  solve_cert (cert1 A D E F [] [0] 1 1).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB0RA_0RC1RE_1LF0RD_0RE---_1RB0RC_0LF0LA").
Lemma nonhalt7:~halts tm7 c0.
Proof.
  solve_cert (cert1 E F A D [] [0;0] 1 1).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB0RC_0RA0RB_1RD0RE_1LD1RC_1LF---_0LF0LB").
Lemma nonhalt8:~halts tm8 c0.
Proof.
  solve_cert (cert1 C F B A [] [0] 1 1).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1RB0RC_0RC1RA_1LD---_0RE0RD_0RA1LF_0LF0LD").
Lemma nonhalt9:~halts tm9 c0.
Proof.
  solve_cert (cert1 A F D E [] [0] 1 1).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1RB0RC_0RC1RA_1LD---_0LD0LE_0RF0RE_1LE0RA").
Lemma nonhalt10:~halts tm10 c0.
Proof.
  solve_cert (cert1 A D E F [] [0] 1 1).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1RB0RC_1LB1RA_1LD---_0RE0RD_0RA1LF_0LF0LD").
Lemma nonhalt11:~halts tm11 c0.
Proof.
  solve_cert (cert1 A F D E [] [0] 1 1).
Qed.


