From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounterFull.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import UnaryCounter.

Open Scope list.

Module Eat1Digit.
Section Eat1Digit.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR d0 d1 d1a:list Sym.
Hypothesis R: nat->nat->side.
Hypothesis a0:N.
Hypothesis n_init:positive.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Notation "l |> r" :=
  (l <* qR {{QR}}> r) (at level 30).

Definition L n := BinaryCounter d0 d1 (d1a *> const 0) n.

Hypothesis LInc:
  forall r n,
    L n <| r -->+
    L (Pos.succ n) |> r.

Hypothesis RInc:
  forall l n m,
    l |> R (1+n) m -->+
    l <| R n (1+m).

Hypothesis ROv:
  forall n m,
    L (Pos.of_nat (N.to_nat ((Npos n)*2+a0))) |> R 0 m -->+
    L n <| R (1+m) 0.

Lemma RIncs k n m:
  L k |> R n m -->*
  L (Pos.of_nat (N.to_nat ((Npos k)+(N.of_nat n)))) |> R 0 (n+m).
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
  L (Pos.of_nat (N.to_nat ((Npos n)*2+a0))) |> R 0 ((Pos.to_nat n)+(N.to_nat a0)).

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

End Eat1Digit.


Inductive Cert :=
| cert1
  (QL QR : Q)
  (qL qR d0 d1 d1a : list Sym)
  (R: nat->nat->side)
  (a0 : N)
  (n_init : positive).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL ?QR
  ?qL ?qR ?d0 ?d1 ?d1a
  ?R
  ?a0
  ?n_init) =>
  eapply (nonhalt _
    QL QR
    qL qR d0 d1 d1a
    R
    a0
    n_init);
  [ intros;
    apply LInc';
    try (execute_with_shift_rule || fail)
  | try (execute_with_shift_rule || fail)
  | intros;
    unfold L;
    repeat (rewrite Pos_mul2 || rewrite Pos_mul2add1);
    cbn[BinaryCounter];
    try (execute_with_shift_rule || fail)
  | unfold config,L; cbn;
    cbv[Pos.to_nat];
    cbv[Pos.iter_op];
    cbn;
    try (solve_init || fail)
  ]
end.


Definition tm0 := Eval compute in (TM_from_str "1RB1LF_1RC0RB_1RD1RB_0LE0LF_---0LF_1LA1LD").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 A C [1;0] [1;0] [0;0] [1;0] [1;0] (fun n m => [1;0]^^m *> [0;1]^^n *> const 0) 1 2).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1LB0LA_1RC0LA_0LE0RD_0RC1LF_1RB0LD_1LE---").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 B C [1;0;0] [1;1;0] [0;0] [1;0] [1;0] (fun n m => [1;0;0]^^m *> [1] *> [0;1;1]^^n *> const 0) 0 1).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB0RB_1LC0RB_0LD1LC_1RA0LE_1LF0RE_0LA---").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 C B [] [] [0;0] [1;1] [1;1] (fun n m => [1;1;1;0]^^(1+m) *> [0;1;1;0]^^n *> [1] *> const 0) 0 1).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1LB1LC_1RC0LE_1LE0RD_1RB0RC_0RF0LA_1LA---").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 B D [1] [0] [0;0] [1;0] [1;0] (fun n m => [0;0;1]^^m *> [0;1;1]^^n *> [0;1] *> const 0) 0 1).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1LB1LC_1RC0LE_1LE0RD_1RB0RD_0RF0LA_1LA---").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 B D [1] [0] [0;0] [1;0] [1;0] (fun n m => [0;0;1]^^m *> [0;1;1]^^n *> [0;1] *> const 0) 0 1).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1LB---_1LC1LF_1RD0LB_1LB0RE_0RD1RC_1LC1LA").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 C D [] [] [0;0] [1;0] [1;0] (fun n m => [1;1;0]^^m *> [1;1;1]^^n *> const 0) 1 1).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1LD_1RC0LE_1LA0RF_---1LC_1LB1LE_0RC1RB").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 B C [] [] [0;0] [1;0] [1;0] (fun n m => [1;1;0]^^(1+m) *> [1;1;1]^^n *> const 0) 0 1).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1LB0RE_1RC1LF_1LD1LC_1RA0LC_0RA1RD_---1LA").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 D A [] [] [0;0] [1;0] [1;0] (fun n m => [1;1;0]^^(m) *> [1;1;1]^^n *> const 0) 0 1).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1LB0RE_1LC1LF_1LD1LC_1RA0LC_0RA1RD_---1LA").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 D A [] [] [0;0] [1;0] [1;0] (fun n m => [1;1;0]^^(m) *> [1;1;1]^^n *> const 0) 0 1).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1RB1LE_1RC0RB_0LC1LD_0LE1RD_0LA1LF_---1LA").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_cert (cert1 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1;0;0] (fun n m => [1;0;1;0]^^n *> [0;1;0;1] *> [0;1;0;1]^^m *> const 0) 0 1).
  all: follow H; execute_with_shift_rule.
Qed.

Definition tm10 := Eval compute in (TM_from_str "1RB1LD_1RC0RB_0LD1RC_0LA1LE_0LF1LA_0LA---").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_cert (cert1 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1;0;0] (fun n m => [1;0;1;0]^^n *> [0;1;0;1] *> [0;1;0;1]^^m *> const 0) 0 1).
  all: follow H; execute_with_shift_rule.
Qed.

Definition tm11 := Eval compute in (TM_from_str "1RB1LD_1RC0RB_0LD1RC_0LA1LE_0LF1LA_0RC---").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_cert (cert1 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1;0;0] (fun n m => [1;0;1;0]^^n *> [0;1;0;1] *> [0;1;0;1]^^m *> const 0) 0 1).
  all: follow H; execute_with_shift_rule.
Qed.

Definition tm12 := Eval compute in (TM_from_str "1LB0LE_1RC1LB_1RD0RC_1LA0LF_1LD---_0LE0RA").
Lemma nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 B C [] [] [0] [1] [1] (fun n m => [1;1;1] *> [0;1;1]^^m *> [0;0;1]^^n *> [0;1] *> const 0) 0 1).
Qed.

Definition tm13 := Eval compute in (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB---_1LB0LA_---1LA").
Lemma nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 B B [1;1;0] [1;1;0] [1;1;0] [0;1;0] [] (fun n m => [1] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0]^^(1+m) *> const 0) 0 1).
Qed.

Definition tm14 := Eval compute in (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB---_0RF0LA_---1LA").
Lemma nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 B B [1;1;0] [1;1;0] [1;1;0] [0;1;0] [] (fun n m => [1] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0]^^(1+m) *> const 0) 0 1).
Qed.

Definition tm15 := Eval compute in (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB1LA_0RD0LA_---1LA").
Lemma nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 B B [1;1;0] [1;1;0] [1;1;0] [0;1;0] [] (fun n m => [1] *> [1;0;1;0]^^n *> [0] *> [1;0;1;0]^^(1+m) *> const 0) 0 1).
Qed.

Definition tm16 := Eval compute in (TM_from_str "1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC1RF_---0RC").
Lemma nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 D B [1;1;1;1;0] [1;0;0;0;0] [0;0;0] [1;0;0] [1] (fun n m => [1;1;1;0;0]^^(m) *> [0;1;1;1;0]^^(n) *> const 0) 1 1).
Qed.

(*

*)
End Eat1Digit.
