From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Section FractalType1v2.
Hypothesis tm:TM.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL:Q.
Hypothesis qL w1 w1a:list Sym.
Hypothesis R:nat->nat->side.
Hypothesis c1 c2 base:nat.

Notation "l <| r" :=
  (l <{{QL}} qL *> r) (at level 30).

Hypothesis w1_all0:
  w1 *> const 0 = const 0.

Hypothesis Inc:
  forall l a b c,
    l <* w1^^((1+base)+a) <| R (b) (1+c) -->*
    l <* w1^^(a) <| R (1+b) c.

Hypothesis LROv:
  forall l b,
    l <* w1a <| R b 0 -->*
    l <| R 0 (c1+b*(2+base)).

Hypothesis ROv:
  forall l b,
    l <* w1^^c1 <| R (c2+b) 0 -->+
    l <* w1a <* w1^^(b*(2+base)) <| R c2 0.

Hypothesis init:
  c0 -->*
  const 0 <| R c2 0.

Lemma Incs l b c:
  l <* w1^^((1+base)*c) <| R b c -->*
  l <| R (c+b) 0.
Proof.
  remember (1+base) as v1.
  gen b.
  induction c; intros.
  - rewrite Nat.mul_0_r.
    finish.
  - rewrite <-mult_n_Sm.
    rewrite Nat.add_comm.
    follow Inc.
    follow IHc.
    finish.
Qed.

Definition N x := c1+c2*(1+base)+x*(2+base).

Lemma nxt n:
  (forall l,
   l <* w1^^(n*(2+base)) <| R c2 0 -->*
   l <| R (c2+n) 0) ->
  (forall l,
   l <* w1^^((N n)*(2+base)-n*(2+base)) <| R (c2+n) 0 -->+
   l <| R (c2+(N n)) 0).
Proof.
  pose proof Incs as HIncs.
  unfold N.
  remember (1+base) as v1.
  remember (2+base) as v2.
  replace ((c1+c2*v1+n*v2)*v2-n*v2) with (c1+v1*(c1+(c2+n)*v2)) by lia.
  intros H l.
  simpl_tape.
  follow10 ROv.
  follow H.
  follow LROv.
  follow HIncs.
  finish.
Qed.

Lemma nxt' n:
  (forall l,
   l <* w1^^(n*(2+base)) <| R c2 0 -->*
   l <| R (c2+n) 0) ->
  (forall l,
   l <* w1^^((N n)*(2+base)) <| R (c2) 0 -->+
   l <| R (c2+(N n)) 0).
Proof.
  intros H l.
  assert ((N n)*(2+base) >= n*(2+base)) by (unfold N; lia).
  replace ((N n)*(2+base)) with (n*(2+base)+((N n)*(2+base)-n*(2+base))) by lia.
  simpl_tape.
  follow H.
  apply nxt,H.
Qed.

Fixpoint Ns(n:nat) :=
match n with
| O => O
| S n0 => N (Ns n0)
end.

Lemma Ns_spec n:
   (forall l,
    l <* w1^^((Ns (S n))*(2+base)-(Ns n)*(2+base)) <| R (c2+(Ns n)) 0 -->+
    l <| R (c2+(Ns (S n))) 0) /\
   (forall l,
    l <* w1^^((Ns (S n))*(2+base)) <| R (c2) 0 -->+
    l <| R (c2+(Ns (S n))) 0).
Proof.
  induction n; intros.
  - split; [apply nxt | apply nxt']; intros; cbn[Ns]; finish.
  - destruct IHn as [IHn IHn'].
    split; [apply nxt | apply nxt']; intros; follow100 IHn'; finish.
Qed.

Definition config n := const 0 <| R (c2 + Ns n) 0.

Lemma BigStep n:
  config n -->+
  config (S n).
Proof.
  unfold config.
  cbn[Ns].
  destruct (Ns_spec n) as [H _].
  specialize (H (const 0)).
  rewrite lpow_all0 in H; auto.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  apply multistep_nonhalt with (c':=config 0).
  - unfold config.
    cbn[Ns].
    follow init.
    finish.
  - apply progress_nonhalt_simple.
    intro i.
    eexists.
    apply BigStep.
Qed.

End FractalType1v2.

Inductive Cert :=
| cert1
  (QL : Q)
  (qL w1 w1a : list Sym)
  (R: nat->nat->side)
  (c1 c2 base : nat).

Ltac solve_cert cert :=
match cert with
  (cert1
  ?QL
  ?qL ?w1 ?w1a
  ?R
  ?c1 ?c2 ?base) =>
  eapply (nonhalt _
    QL
    qL w1 w1a
    R
    c1 c2 base);
  [ solve_const0_eq
  | try (execute_with_shift_rule; fail)
  | intros; simpl_tape;
    rewrite lpow_mul;
    try (execute_with_shift_rule; fail)
  | intros; simpl_tape;
    rewrite lpow_mul;
    try (execute_with_shift_rule; fail)
  | cbn;
    try (solve_init; fail)
  ]
end.

Definition tm0 := Eval compute in (TM_from_str "1RB0RF_0RC0LD_0LD1RA_1LB1LE_1RE1LD_---0RA").
Lemma nonhalt0: ~halts tm0 c0.
Proof.
  solve_cert (cert1 B [1] [0] [1;0]
    (fun b c => [1;1]^^b *> [0] *> [1]^^c *> const 0)
    1 1 0).
Qed.

Definition tm1 := Eval compute in (TM_from_str "1RB1LD_0RC0RB_0LD0RE_0LA---_0LF1LE_1LF1LA").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1 A [] [0] [0;1;0]
    (fun b c => [1;1]^^b *> [0;1] *> [1]^^c *> const 0)
    3 0 0).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1LB0LE_1RC0LB_1RB0RD_0LE0RD_1LA1LF_---1LE").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1 B [0] [0] [0;0;0;1]
    (fun b c => [0;0]^^(b) *> [1]^^c *> [0;1] *> const 0)
    4 2 0).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB0RA_0RC0LD_0LD1RA_1LB1LE_1LF1LD_1RE---").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1 B [1] [0] [0;1;0]
    (fun b c => [1;1]^^(b) *> [0;1] *> [1]^^c *> const 0)
    2 2 0).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1LB---_0RC1LE_1LF1RD_0RE0RD_0LA0LF_1LC1LA").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1 B [] [0] [1;0;0;0]
    (fun b c => [1;1]^^(2+b) *> [0] *> [1]^^c *> const 0)
    3 0 0).
Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB0RA_0LC0LF_1LF1LD_1RE0LE_---1RA_1LC1LC").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1 D [] [0] [0;1;1]
    (fun b c => [1;1]^^(1+b) *> [0;1] *> [1]^^c *> const 0)
    2 0 0).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1LB1RC_0RA1RD_0RD0RC_0LA0LE_1LF1LA_1LE---").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1 B [] [0] [1;0]
    (fun b c => [1;1]^^(1+b) *> [0] *> [1]^^c *> const 0)
    1 0 0).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1RB0LF_0LC---_1RD0LD_1LC1RE_0RA0RE_1LF1LD").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1 D [1;1] [0;0] [0;1;1]
    (fun b c => [1;1;1;1]^^(b) *> [0] *> [1;1]^^c *> const 0)
    1 1 0).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1RB0RA_0RC0LD_0LD1RA_1LB1LE_1LF1LD_1LE---").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1 B [1] [0] [1;0]
    (fun b c => [1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    1 1 0).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1RB0LE_0LC0RD_1LA1LB_0RA0RB_1LE1LF_0LD---").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1 D [0;1;1;1] [0] [1;0;0]
    (fun b c => [1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    2 0 0).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1RB0LF_0LC0RE_1LD1LB_0LE---_0RA0RB_1LF1LD").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1 E [0;1;1;1] [0] [1;0;0]
    (fun b c => [1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    2 0 0).
Qed.

Definition tm11 := Eval compute in (TM_from_str "1RB0RF_0RC0LD_0LD1RA_1LB1LE_1LE1LD_---0RA").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1 B [1] [0] [1;0]
    (fun b c => [1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    1 1 0).
Qed.

Definition tm12 := Eval compute in (TM_from_str "1LB---_1RC0LB_1RB0RD_0LE0RD_1LF1LE_1LA0LE").
Lemma nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1 B [0] [0] [0;0;0;0;1]
    (fun b c => [0;0]^^(b) *> [1]^^c *> [0;1] *> const 0)
    5 3 0).
Qed.

Definition tm13 := Eval compute in (TM_from_str "1LB---_1LC0LF_1RD0LC_1RC0RE_0LF0RE_1LA1LF").
Lemma nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1 C [0] [0] [0;0;0;0;1]
    (fun b c => [0;0]^^(b) *> [1]^^c *> [0;1;1] *> const 0)
    5 3 0).
Qed.

Definition tm14 := Eval compute in (TM_from_str "1LB---_1RC0LA_1RD0RB_0LE0RD_1LF0LE_1LC1LE").
Lemma nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1 B [1;0;1] [0;0] [0;0;0;1]
    (fun b c => [0;1;0;1]^^(b) *> [1;1]^^c *> const 0)
    2 2 0).
Qed.

Definition tm15 := Eval compute in (TM_from_str "1RB0LD_1LC0RA_1LD1LB_1RE---_0LF0RE_0LB1LA").
Lemma nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1 A [1;0;1] [0;0] [0;1]
    (fun b c => [0;1;0;1]^^(b) *> [1;1]^^c *> const 0)
    2 0 0).
Qed.

Definition tm16 := Eval compute in (TM_from_str "1RB0LD_1RC0RA_0LA0RC_1LA1LE_1LF---_1LB1LE").
Lemma nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1 A [1;0] [0;0] [0;0;0;1]
    (fun b c => [1;0;1;0]^^(b) *> [1;1]^^c *> const 0)
    2 1 0).
Qed.

Definition tm17 := Eval compute in (TM_from_str "1LB---_0LC1LA_1RC0RD_0RE0RC_0LA0LF_1LF1LB").
Lemma nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1 C [0;1;1;1] [0] [1;1;0]
    (fun b c => [1;1;1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    2 0 2).
Qed.

Definition tm18 := Eval compute in (TM_from_str "1LB---_0LC1LA_1RC0RD_0RE0RC_0LA0LF_1LF0RB").
Lemma nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1 C [0;1;1;1] [0] [1;1;0]
    (fun b c => [1;1;1;1]^^(b) *> [0] *> [1]^^c *> const 0)
    2 0 2).
Qed.


