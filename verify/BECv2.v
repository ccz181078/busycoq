From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.

Open Scope list.

Module Eat2Digit.
Section Eat2Digit.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR d1 w0 w1 w2:list Sym.
Hypothesis a0 a1:N.
Hypothesis n_init:nat.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition L n := BinaryCounter_0 d1 n.

Definition R n m := w0^^n *> w1 *> w2^^m *> const 0.

Hypothesis LInc:
  forall r n,
    L n <| r -->+
    L (N.succ n) |> r.

Hypothesis RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).

Hypothesis ROv:
  forall n m,
    L ((n*2+a0)*2+a1) |> R 0 m -->+
    L n <| R (3+m) 0.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (k+(N.of_nat n)) |> R 0 (n+m).
Proof.
  gen k m.
  induction n; intros.
  - finish.
  - follow100 RInc.
    follow100 LInc.
    follow IHn.
    finish.
Qed.

Definition config n :=
  L (((N.of_nat n)*2+a0)*2+a1) |> R 0 (n*3+(N.to_nat (a0*2+a1))).

Lemma BigStep n:
  config n -->+
  config (1+n).
Proof.
  unfold config.
  follow10 ROv.
  follow100 LInc.
  follow RIncs.
  finish.
Qed.

Hypothesis init:
  c0 -->*
  config n_init.

Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config n_init).
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  eexists.
  apply BigStep.
Qed.

End Eat2Digit.

Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR d1 w0 w1 w2 : list Sym)
  (a0 a1 : N)
  (n_init : nat).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR ?d1 ?w0 ?w1 ?w2
  ?a0 ?a1
  ?n_init) =>
  eapply (nonhalt _
    QL QR
    qL qR d1 w0 w1 w2
    a0 a1
    n_init);
  [ intros;
    apply LInc_0;
    try (execute_with_shift_rule || fail)
  | try (execute_with_shift_rule || fail)
  | intros;
    unfold L;
    repeat (rewrite BinaryCounter_0_d0' || rewrite BinaryCounter_0_d1');
    try (execute_with_shift_rule || fail)
  | unfold config,L,R,BinaryCounter_0; cbn;
    try (solve_init || fail)
  ]
end.


Definition tm0 := Eval compute in (TM_from_str "1LB0LE_0LC1LD_1RA1LC_1RC---_1RF1LE_0RA0RF").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 E A [1;0] [0;0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1LB0LE_0LC1LD_1RA1LC_1LC---_1RF1LE_0RA0RF").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 E A [1;0] [0;0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1LB1LE_0LC1LD_1RA1LC_1RC---_1RF0LE_0RF0RA").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 E A [0;1] [0;0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1LB1LE_0LC1LD_1RA1LC_1LC---_1RF0LE_0RF0RA").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 E A [0;1] [0;0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD0LA_0LE1LF_1RC1LE_---1LE").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 A C [1;0] [0;0] [1] [1] [0] [1] 0 1 0).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1LA_0RC0RB_1LD0LA_0LE1LF_1RC1LE_---1RE").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 A C [1;0] [0;0] [1] [1] [0] [1] 0 1 0).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1LB1RA_1LC0LD_1RD---_0LE1LD_1RF1LE_0RA0RF").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 E A [0] [0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1LB1RA_1LC0LD_1RD---_1LE1LD_1RF0LE_0RF0RA").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 E A [1] [0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1LB1RA_1LC0LD_1LD---_0LE1LD_1RF1LE_0RA0RF").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 E A [0] [0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1LB1RA_1LC0LD_1LD---_0LE1LD_1RF1LE_0RA0RF").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 E A [0] [0] [1] [1] [0] [1] 0 0 0).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1LB1RA_1LC0LD_1LD---_1LE1LD_1RF0LE_0RF0RA").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 E A [1] [0] [1] [1] [0] [1] 0 0 0).
Qed.




End Eat2Digit.
