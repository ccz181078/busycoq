From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Section FractalType2.
Hypothesis tm:TM.
Hypothesis QL QR:Q.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l |> r" :=
  (l {{QR}}> r) (at level 30).

Notation "l <| r" :=
  (l <{{QL}} r) (at level 30).

Definition R n m := [1]^^n *> [0] *> [1]^^m *> const 0.

Hypothesis Inc:
  forall l n m,
    l |> R (4+n) m -->*
    l <* [1;1] |> R n (2+m).

Hypothesis Ov1:
  forall l m,
    l |> R 1 (1+m) -->*
    l <* [1;0;0] |> R m 0.

Hypothesis Ov0:
  forall l m,
    l |> R 0 (1+m) -->*
    l <* [1]^^2 |> R m 0.

Hypothesis Ov3:
  forall l n m,
    l <* [1]^^n |> R 3 (m) -->*
    l <| R (2+n+m) 2.

Hypothesis LR:
  forall l r,
    l <* [1;0] <| r -->+
    l <* [1]^^2 |> r.

Hypothesis Ls:
  forall l r n,
    l <* [1]^^n <| r -->*
    l <| [1]^^n *> r.

Lemma Incs n c m l:
  l |> R (n*4+c) m -->*
  l <* [1]^^(n*2) |> R c (n*2+m).
Proof.
  gen l c m.
  induction n; intros.
  1: finish.
  replace (S n*4+c) with (4+(n*4+c)) by lia.
  follow Inc.
  follow IHn.
  simpl_tape.
  simpl_rotate.
  finish.
Qed.

Lemma R_1s k n m:
  [1]^^k *> R n m = R (k+n) m.
Proof.
  unfold R.
  simpl_tape.
  reflexivity.
Qed.

Definition P n :=
  (forall l,
    l |> R (n*4+1) 0 -->*
    l <| R (n*8) 2).

Lemma nxt0 n:
  P n ->
  (forall l,
    l <* [1;0;0] |> R (n*4+1) 0 -->*
    l <| R (n*12+6) 2).
Proof.
  intros H l.
  follow H.
  change [1;0;0] with ([1;0]++[0]).
  rewrite Str_app_assoc.
  follow100 LR.
  replace (n*8) with ((n*2)*4+0) by lia.
  follow Incs.
  replace (n*2*2+2) with (1+(n*4+1)) by lia.
  follow Ov0.
  follow H.
  follow Ls.
  follow Ls.
  rewrite <-(Str_app_assoc ([1]^^2) [0]).
  change (([1]^^2)++[0]) with ([1]^^1++[1;0]).
  rewrite Str_app_assoc.
  follow Ls.
  follow100 LR.
  repeat rewrite R_1s.
  replace (1+(n*2*2+(2+n*8))) with (n*3*4+3) by lia.
  follow Incs.
  follow Ov3.
  follow Ls.
  rewrite R_1s.
  finish.
Qed.

Lemma nxt1 n:
  P n ->
  P (n*2+1).
Proof.
  intros H l.
  follow Incs.
  replace ((n*2+1)*2+0) with (1+(n*4+1)) by lia.
  follow Ov1.
  follow (nxt0 _ H).
  follow Ls.
  repeat rewrite R_1s.
  finish.
Qed.

Definition config0 n :=
  const 0 <* [1]^^(n*4+2) <* [1;0;0] |> R (n*4+1) 0.

Lemma nxt2 n:
  P n ->
  ( config0 n -->+
    config0 (n*2+1)).
Proof.
  unfold config0.
  intros H.
  follow (nxt0 _ H).
  replace ([1]^^(n*4+2) *> const 0) with ([1]^^(n*4+1) *> [1;0] *> const 0). 2:{
    simpl_tape.
    simpl_rotate.
    reflexivity.
  }
  follow Ls.
  follow10 LR.
  rewrite R_1s.
  replace (n*4+1+(n*12+6)) with ((n*4+1)*4+3) by lia.
  follow Incs.
  follow Ov3.
  replace ([1]^^2 *> const 0) with ([1]^^1 *> [1;0] *> const 0). 2:{
    simpl_tape.
    reflexivity.
  }
  follow Ls.
  follow100 LR.
  rewrite R_1s.
  replace (1+(2+(n*4+1)*2+((n*4+1)*2+2))) with ((n*4+2)*4+1) by lia.
  follow Incs.
  replace ((n*4+2)*2+2) with (1+((n*2+1)*4+1)) by lia.
  follow Ov1.
  simpl_tape.
  simpl_rotate.
  finish.
Qed.

Fixpoint Ns(n:nat):nat :=
match n with
| O => 1
| S n0 => (Ns n0)*2+1
end.

Definition config n :=
  config0 (Ns n).

Hypothesis P1: P 1.

Hypothesis init:
  c0 -->* config 0.

Lemma Ns_spec n: P (Ns n).
Proof.
  induction n; intros.
  - apply P1.
  - apply nxt1,IHn.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 0).
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  exists (S i).
  apply nxt2,Ns_spec.
Qed.

End FractalType2.


Inductive Cert :=
| cert1
  (QL QR: Q).


Ltac solve_cert cert :=
match cert with
  (cert1 ?QL ?QR) =>
  eapply (nonhalt _ QL QR);
  [ unfold R;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold R;
    try (execute_with_shift_rule; fail)
  | unfold P,R;
    intros;
    step1s
  | unfold config,config0,Ns,R;
    solve_init ]
end.




Definition tm0 := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RA0RE_0RB0RF_---0LA").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 A D).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RA0RE_0RB0RF_---1LB").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 A D).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_0RA0RE_0RB1RF_---0RC").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 A D).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB0RF_---1LB").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 A D).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RB0RE_0RB1RF_---0RC").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 A D).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0LA_1LC---_0RA0RF_0RB0RC").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 A E).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0LA_1LC---_0RA0RF_0RB0LF").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 A E).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0LA_1LC---_1RB0RF_0RB0LF").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 A E).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB0RF_---0LA").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 D A).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1RB0RE_0RC1RA_1LC0LD_1RB1LD_0RB0RF_---0LD").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 D A).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1RB0RF_0RC1RA_1LD0LE_1LC---_1RB1LE_0RB0RC").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 E A).
Qed.










