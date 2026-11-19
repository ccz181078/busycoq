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

Lemma BinaryCounter_0_full n d1:
  BinaryCounter_0 d1 (Npos (pow2' n)) = d1^^(1+n) *> const 0.
Proof.
  induction n.
  - unfold d1a.
    cbn.
    simpl_tape.
    reflexivity.
  - cbn.
    cbn in IHn.
    rewrite IHn.
    simpl_tape.
    reflexivity.
Qed.

Section FractalBEC.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR d1 w1 w0:list sym.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition L n := BinaryCounter_0 d1 n.

Definition R n m r := w1^^n *> w0 *> w1^^m *> r.

Hypothesis LInc:
  forall r n,
    L n <| r -->+
    L (N.succ n) |> r.

Hypothesis RInc:
  forall l r n m,
    l |> R (1+n) m r -->+
    l <| R n (1+m) r.

Lemma Incs k n m r:
  L (N.of_nat k) <| R n m r -->+
  L (N.of_nat (1+k+n)) |> R 0 (n+m) r.
Proof.
  follow10 LInc.
  gen k m.
  induction n; intros.
  - finish.
  - follow100 RInc.
    follow100 LInc.
    follow (IHn (1+k) (1+m)).
    finish.
Qed.

Hypothesis Ov:
  forall r n m,
    L (Npos (pow2' n)) |> R 0 m r -->*
    const 0 <| (w0^^n *> w1^^(2+m) *> r).

Definition f i :=
  (N.to_nat (Npos (pow2' i) - 1)).

Definition P0 i :=
  forall r,
  const 0 <| w0^^i *> r -->*
  const 0 <| w1^^f i *> r.

Definition P1 i :=
  forall r,
  const 0 <| w1^^f i *> w0 *> r -->+
  const 0 <| w1^^f (1+i) *> r.

Lemma nxtP1 i:
  P0 i ->
  P1 i.
Proof.
  unfold P0,P1,f.
  intros HP0 r.
  remember (N.to_nat (N.pos (pow2' i) - 1)) as n.
  follow10 (Incs 0 n 0 r).
  replace (N.of_nat (1+0+n)) with (Npos (pow2' i)) by lia.
  follow Ov.
  follow HP0.
  cbn[Nat.add].
  cbn[pow2'].
  replace (N.to_nat (N.pos (pow2' i)~1 - 1)) with (2+n+n) by lia.
  simpl_tape.
  finish.
Qed.

Lemma P0nxt i:
  P0 i ->
  P0 (1+i).
Proof.
  unfold P0.
  intros HP0 r.
  replace (1+i) with (i+1) by lia.
  rewrite lpow_add,Str_app_assoc.
  follow HP0.
  pose proof (nxtP1 i HP0) as HP1.
  unfold P1 in HP1.
  simpl_tape.
  follow100 HP1.
  finish.
Qed.

Lemma P0_0:
  P0 0.
Proof.
  unfold P0.
  es.
Qed.

Lemma P0_spec i:
  P0 i.
Proof.
  induction i.
  - apply P0_0.
  - apply P0nxt,IHi.
Qed.

Definition config i :=
  const 0 <| w1^^f i *> const 0.

Hypothesis w0_all0:
  w0 *> const 0 = const 0.

Lemma config_S i:
  config i -->+ config (S i).
Proof.
  unfold config.
  epose proof (nxtP1 i (P0_spec i) (const 0)) as HP1.
  rewrite w0_all0 in HP1.
  follow10 HP1.
  finish.
Qed.

Hypothesis init:
  c0 -->*
  config 0.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intro i. eexists.
  apply config_S.
Qed.

End FractalBEC.


Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR d1 w1 w0 : list Sym).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR ?d1 ?w1 ?w0) =>
  eapply (nonhalt _
    QL QR
    qL qR d1 w1 w0);
  [ intros;
    apply LInc_0;
    try (es; fail)
  | unfold R;
    intros;
    try (es; fail)
  | intros;
    unfold L,R;
    rewrite BinaryCounter_0_full;
    try (es; fail)
  | solve_const0_eq
  | unfold config,f;
    cbn;
    try (es; fail)
  ]
end.


Definition tm1 := Eval compute in (TM_from_str "1LB0LF_1LC0LE_1RD1LB_1RA0RD_1LA---_0LA0RB").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 B D [1] [0] [0;1] [1;0;1] [0;0]).
Qed.


Definition tm2 := Eval compute in (TM_from_str "1RB0LF_1LC---_1RE0LD_0LC1LF_0RE1RA_0LA0RC").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 D A [0;1] [1;0] [0;1] [1;0;1] [0;0]).
Qed.


Definition tm3 := Eval compute in (TM_from_str "1LB0LC_1RB1LC_0LA0RD_1RF1LE_1LD---_1RA0RF").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 D A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm4 := Eval compute in (TM_from_str "1LB0LE_1LC1LE_1RD1LB_1RA0RD_0LA0RF_1RD---").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1LB0LE_1LC1LE_1RD0LF_1RA0RD_0LA0RC_0RA---").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm6 := Eval compute in (TM_from_str "1LB0LE_1LC1LE_1RD1LF_1RA0RD_0LA0RC_1LC---").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm7 := Eval compute in (TM_from_str "1LB0LF_0RC1LF_1RE1LD_1LC---_1RA0RE_0LA0RC").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm8 := Eval compute in (TM_from_str "1LB0LF_0LC1LF_1RD0LB_0RD0RE_1RA---_0LA0RC").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 C A [0;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm9 := Eval compute in (TM_from_str "1LB0LF_1LC1LE_1RD1LB_1RA0RD_0LA---_0LA0RC").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm10 := Eval compute in (TM_from_str "1LB0LF_1LC1LF_1RD1LB_---0RE_1RA0RE_0LA0RC").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 C A [1;1;0] [1;0;0] [1;0] [1;1;0] [0;0]).
Qed.


Definition tm11 := Eval compute in (TM_from_str "1LB1LF_1RC1LA_0RD0RC_1RE---_0LA0LF_0LE0RB").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 B E [1;0;0] [1;0;0] [1;0] [1;0;0] [0;0]).
Qed.


