From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

Open Scope list.

Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.

Ltac es :=
  repeat rewrite lpow_add;
  repeat rewrite Str_app_assoc;
  repeat rewrite lpow_mul;
  execute_with_shift_rule.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

Ltac simpl_add_mul :=
  repeat (
    rewrite Nat.mul_add_distr_r ||
    rewrite Nat.mul_sub_distr_r ||
    rewrite Nat.add_assoc ||
    rewrite <-Nat.mul_assoc
    ).

Section Loop3v1.

Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis c1 c2 c3 c4 c5 c6 c7:nat.
Hypothesis x0 x1 x2:nat.
Hypothesis S0 S1:nat->nat->nat->Q*tape.

Hypothesis Inc0:
  forall a b c,
    S0 (1+a) b (1+c) -->*
    S0 a (2+b) c.

Hypothesis Inc1:
  forall a b c,
    S1 (1+a) b c -->*
    S1 a (1+b) (1+c).

Hypothesis ROv0:
  forall a b,
    S0 (c1+a) (b) 0 -->+
    S1 a (c2+b) c3.

Hypothesis LOv1:
  forall b c,
    S1 0 (c4+b) (c6+c) -->*
    S0 (c5+b) x1 (c7+c).

Hypothesis init:
  c0 -->*
  S0 x0 x1 x2.

Lemma Inc0s a b c n:
  S0 (n+a) b (n+c) -->*
  S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc0.
Qed.

Lemma Inc1s a b c:
  S1 a b c -->*
  S1 0 (a+b) (a+c).
Proof.
  gen b c.
  ind a Inc1.
Qed.

Definition config(x:nat*nat):=
  let (a,c):=x in
  S0 a x1 c.

Definition P(x:nat*nat):Prop :=
  let (a,c):=x in
  c1+c <= a /\
  c1+c4 <= a+c+c2+x1 /\
  c1+c6+c <= a+c3.

Definition nxt(x:nat*nat):=
  let (a,c):=x in
  (a+c+c2+c5+x1-c1-c4,a-c+c3+c7-c1-c6).

Hypothesis Pnxt:
  forall x,
  P x ->
  P (nxt x).

Hypothesis Pinit:
  P (x0,x2).


Lemma nonhalt:~halts tm c0.
  apply multistep_nonhalt with (c':=config (x0,x2)).
  1: apply init.
  eapply progress_nonhalt_cond.
  2: apply Pinit.
  intro i.
  intros HP.
  exists (nxt i).
  split.
  2: auto.
  destruct i as [a c].
  cbn.
  unfold P in HP.
  follow (Inc0s (c1+(a-c-c1)) x1 0 c).
  follow10 ROv0.
  follow Inc1s.
  replace (a-c-c1+(c2+(c*2+x1))) with (c4+(a+c+c2+x1-c1-c4)) by lia.
  replace (a-c-c1+c3) with (c6+(a-c-c1+c3-c6)) by lia.
  follow LOv1.
  finish.
Qed.

End Loop3v1.

Inductive Cert :=
| cert1(c1 c2 c3 c4 c5 c6 c7 x0 x1 x2:nat)(S0 S1:nat->nat->nat->Q*tape)
.

Ltac solve_cert cert :=
match cert with
  (cert1
  ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
  ?x0 ?x1 ?x2
  ?S0 ?S1) =>
  eapply (nonhalt _
    c1 c2 c3 c4 c5 c6 c7
    x0 x1 x2
    S0 S1);
  [ es
  | es
  | es
  | es
  | solve_init
  | intros x;
    destruct x as [a c];
    unfold P,nxt;
    try lia
  | unfold P; try lia
  ]
end.

Definition tm1 := Eval compute in (TM_from_str "1RB0RD_0LC0RC_---1LD_0RE1LF_1RA0LF_1RE0LA").
Lemma nonhalt1: ~halts tm1 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 0 1
    4 0 1
    (fun a b c => const 0 <* [1;1;1]^^a <* [0;1;1]^^b <* [1;1;1] {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [0;1;1]^^b <* [0;1;0]^^c <* [1;1;0] {{B}}> const 0)
  ).
Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB0LF_1RC0RE_0LD0RD_---1LE_1RA1LF_0LB0RA").
Lemma nonhalt2: ~halts tm2 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 0 1
    4 0 1
    (fun a b c => const 0 <* [1;1;0]^^a <* [0;1;0]^^b <* [1;1;0] {{C}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [0;1;0]^^b <* [0;1;1]^^c <* [1;1;1] {{C}}> const 0)
  ).
Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB0RD_0LC0RC_---1LD_0RE0LF_1LF1RA_1RE0LA").
Lemma nonhalt3: ~halts tm3 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 0 1
    4 0 1
    (fun a b c => const 0 <* [1;1;0]^^a <* [0;1;0]^^b <* [1;1;0] {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [0;1;0]^^b <* [0;1;1]^^c <* [1;1;1] {{B}}> const 0)
  ).
Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB0RD_0LC0RC_---1LD_1RE0LF_1LF1RA_0LA0RE").
Lemma nonhalt4: ~halts tm4 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 0 1
    4 0 1
    (fun a b c => const 0 <* [1;1;1]^^a <* [0;1;1]^^b <* [1;1;1] {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [0;1;1]^^b <* [0;1;0]^^c <* [1;1;0] {{B}}> const 0)
  ).
Qed.


Definition tm5 := Eval compute in (TM_from_str "1RB1RC_1LC0RE_1RE0LD_1LB0LB_1RF0RA_1RB---").
Lemma nonhalt5: ~halts tm5 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 0 1 0
    2 2 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1RC_1LC0RE_1RE0LD_1LB0LF_1RA0RA_1LC---").
Lemma nonhalt6: ~halts tm6 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 0 1 0
    2 2 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm7 := Eval compute in (TM_from_str "1RB1RC_1LC0RF_1RE0LD_1LB0LB_---0RA_1RA0RA").
Lemma nonhalt7: ~halts tm7 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 0 1 0
    2 2 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm8 := Eval compute in (TM_from_str "1LB---_1RC0LF_0RD1RD_1RE1RB_1LB0RC_0LA1LE").
Lemma nonhalt8: ~halts tm8 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{E}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{E}}> const 0)
  ).
Qed.

Definition tm9 := Eval compute in (TM_from_str "1LB0RC_1RC0LE_1RD0RD_1RA1RB_1LA0LF_1LB---").
Lemma nonhalt9: ~halts tm9 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{A}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{A}}> const 0)
  ).
Qed.

Definition tm10 := Eval compute in (TM_from_str "1LB0RC_1RC0LE_0RF1RD_1RA1RB_0LA1LA_1RA---").
Lemma nonhalt10: ~halts tm10 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{A}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{A}}> const 0)
  ).
Qed.

Definition tm11 := Eval compute in (TM_from_str "1LB0RC_1RC0LE_1RF0RD_1RA1RB_1LA0LA_1RA---").
Lemma nonhalt11: ~halts tm11 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{A}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{A}}> const 0)
  ).
Qed.

Definition tm12 := Eval compute in (TM_from_str "1LB0RF_1RC0LE_---0RD_1RA1RB_1LA0LA_1RD0RD").
Lemma nonhalt12: ~halts tm12 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{A}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{A}}> const 0)
  ).
Qed.

Definition tm13 := Eval compute in (TM_from_str "1LB0RF_1RC0LE_---1RD_1RA1RB_0LA1LA_0RD1RD").
Lemma nonhalt13: ~halts tm13 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 1
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{A}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{A}}> const 0)
  ).
Qed.


Definition tm14 := Eval compute in (TM_from_str "1RB0RB_1LC0RE_1LD0LD_1RE0LB_1RA1RF_---0RD").
Lemma nonhalt14: ~halts tm14 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 1 0
    4 2 1
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [0] {{B}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [1;0;1]^^c <* [1] {{B}}> const 0)
  ).
Qed.


Definition tm15 := Eval compute in (TM_from_str "1LB0RD_0LC1LC_1RD0LA_1RE1RF_0RA1RA_---1RC").
Lemma nonhalt15: ~halts tm15 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 2 1 0
    5 0 2
    (fun a b c => const 0 <* [1;1;0]^^2 <* [1;1;1]^^a <* [1;1;0]^^b {{A}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^2 <* [1;1;1]^^a <* [1;1;0]^^b <* [0;1;0]^^c {{A}}> const 0)
  ).
Qed.


Definition tm16 := Eval compute in (TM_from_str "1RB1RF_1RC0RC_1LD0RA_1LE0LE_1RA0LC_---0RE").
Lemma nonhalt16: ~halts tm16 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 1 0
    3 2 0
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [0] {{C}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [1;0;1]^^c <* [1] {{C}}> const 0)
  ).
Qed.


Definition tm17 := Eval compute in (TM_from_str "1RB---_1LC0RE_1RE0LD_0LB1LB_0RA1RF_1RB1RC").
Lemma nonhalt17: ~halts tm17 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm18 := Eval compute in (TM_from_str "1RB0RB_1RC1RD_1LD0RA_1RA0LE_1LC0LF_1LD---").
Lemma nonhalt18: ~halts tm18 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{C}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{C}}> const 0)
  ).
Qed.

Definition tm19 := Eval compute in (TM_from_str "1RB0RB_1RC1RD_1LD0RA_1RF0LE_1LC0LC_---0RB").
Lemma nonhalt19: ~halts tm19 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{C}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{C}}> const 0)
  ).
Qed.

Definition tm20 := Eval compute in (TM_from_str "1RB1RC_1LC0RF_1RE0LD_0LB1LB_---1RA_0RA1RA").
Lemma nonhalt20: ~halts tm20 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm21 := Eval compute in (TM_from_str "1RB1RC_1LC0RF_1RF0LD_0LE1LB_1LC---_0RA1RA").
Lemma nonhalt21: ~halts tm21 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b {{B}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;1]^^a <* [1;1;0]^^b <* [1;0;0]^^c {{B}}> const 0)
  ).
Qed.

Definition tm22 := Eval compute in (TM_from_str "1RB0RF_1RC---_1LD0RA_1RA0LE_1LC0LC_1RC1RD").
Lemma nonhalt22: ~halts tm22 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 1 0 0
    4 0 3
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b {{C}}> [0;1;0]^^c *> const 0)
    (fun a b c => const 0 <* [1;0;1]^^a <* [1;0;0]^^b <* [1;1;0]^^c {{C}}> const 0)
  ).
Qed.


Definition tm23 := Eval compute in (TM_from_str "1RB1RF_0RC1RC_1LD0RA_0LE1LE_1RA0LC_---1RE").
Lemma nonhalt23: ~halts tm23 c0.
Proof.
  solve_cert (cert1
    1 1 1 0 2 1 0
    3 0 2
    (fun a b c => const 0 <* [1;1;0]^^2 <* [1;1;1]^^a <* [1;1;0]^^b {{C}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^2 <* [1;1;1]^^a <* [1;1;0]^^b <* [0;1;0]^^c {{C}}> const 0)
  ).
Qed.


Definition tm24 := Eval compute in (TM_from_str "1LB0RD_1LC0LC_1RD0LA_1RF1RE_---0RC_1RA0RA").
Lemma nonhalt24: ~halts tm24 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 1 0
    8 2 5
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [0] {{A}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [1;0;1]^^c <* [1] {{A}}> const 0)
  ).
Qed.


Definition tm25 := Eval compute in (TM_from_str "1RB0LD_1RC1RF_1RD0RD_1LE0RB_1LA0LA_---0RA").
Lemma nonhalt25: ~halts tm25 c0.
Proof.
  solve_cert (cert1
    1 2 0 0 0 1 0
    12 2 1
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [0] {{D}}> [0;0;1]^^c *> const 0)
    (fun a b c => const 0 <* [1;1;0]^^a <* [1;0;0]^^b <* [1;0;1]^^c <* [1] {{D}}> const 0)
  ).
Qed.

