
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From Coq Require Uint63.

Ltac er := execute_with_rotate.
Ltac sr := use_shift_rule; simpl_rotate.


Ltac solve_halt :=
  eapply halts_evstep; [|
    repeat (
    repeat ((try simpl_rotate); step1);
    try use_shift_rule);
    constructor
  ];
  apply halted_halts;
  constructor.

Ltac solve_rule:=
  match goal with
  | |- forall _, _ => intros; solve_rule
  | |- (c0 -[ _ ]->* ?S0 _ _ _) => unfold S0; solve_init
  | |- (?S0 _ _ _ -[ _ ]->* ?S0 _ _ _) => unfold S0; execute_with_shift_rule
  | |- (halts _ (?S0 _ _ _)) => unfold S0; solve_halt
  | |- (c0 -[ _ ]->* _) => solve_init
  | |- (_ -[ _ ]->* _) => execute_with_shift_rule
  | |- (halts _ _) => solve_halt
  end.


Lemma Incs(tm:TM)(S0:nat->nat->nat->Q*tape):
  (forall a b c, S0 a (3+b) c -[tm]->* S0 (2+a) (b) (1+c)) ->
  (forall a b c, S0 a b c -[tm]->* S0 (b/3*2+a) (b mod 3) (b/3+c)).
Proof.
  intros H a b c.
  pose proof (Nat.Div0.div_mod b 3) as H0.
  remember (b/3) as b0.
  remember (b mod 3) as b1.
  rewrite H0.
  clear Heqb0 Heqb1 H0 b.
  gen a c.
  induction b0; intros.
  1: finish.
  replace (3*(S b0)+b1) with (3+(3*b0+b1)) by lia.
  follow H.
  follow IHb0.
  finish.
Qed.

Open Scope list.


Ltac solve_calc_step_spec :=
  match goal with
  | |- match (if (?x =? ?x0)%nat then _ else _) with _ => _ end =>
    destruct (Nat.eqb_spec x x0); subst;
    solve_calc_step_spec
  | |- match (match ?x with _ => _ end) with _ => _ end =>
    destruct x;
    solve_calc_step_spec
  | _ => try solve_rule
  end.

Section CubicCup.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Hypothesis S0: nat->nat->nat->Q*tape.

Definition config(x:nat*nat*nat):=
  let '(a,b,c) := x in S0 a b c.

Hypothesis x_init: nat*nat*nat.

Hypothesis calc_step: nat*nat*nat->option (nat*nat*nat).

Hypothesis init: c0 -->* config x_init.

Hypothesis Inc:
  forall a0 b0 c1 : nat, S0 a0 (3 + b0) c1 -->* S0 (2 + a0) b0 (1 + c1).

Hypothesis calc_step_spec:
  forall x,
  match calc_step x with
  | Some y => config x -->* config y
  | None => halts tm (config x)
  end.


Definition calc_Incs(x:nat*nat*nat):nat*nat*nat :=
let '(a,b,c) := x in
(b/3*2+a,b mod 3,b/3+c).

Lemma calc_Incs_spec x:
  config x -->* config (calc_Incs x).
Proof.
  destruct x as [[a b] c].
  unfold config.  
  cbv[calc_Incs].
  apply Incs,Inc.
Qed.

Fixpoint check_halt(x:nat*nat*nat)(T:nat):bool :=
match T with
| O => false
| S T0 =>
  match (calc_step (calc_Incs x)) with
  | None => true
  | Some x' => check_halt x' T0
  end
end.


Lemma check_halt_spec x T:
  check_halt x T = true ->
  halts tm (config x).
Proof.
  gen x.
  induction T; intros.
  - cbn in H.
    congruence.
  - cbn in H.
    pose proof (calc_step_spec (calc_Incs x)) as H0.
    destruct (calc_step (calc_Incs x)) eqn:E.
    + specialize (IHT p H).
      apply (halts_evstep _ _ _ IHT).
      follow (calc_Incs_spec x).
      apply H0.
    + apply (halts_evstep _ _ _ H0).
      apply calc_Incs_spec.
Qed.

Lemma halt:
  forall T,
  check_halt x_init T = true ->
  halts tm c0.
Proof.
  intros T H.
  pose proof (check_halt_spec _ _ H) as H0.
  apply (halts_evstep _ _ _ H0).
  apply init.
Qed.

End CubicCup.


Inductive Cert :=
| cert1
  (S0: nat->nat->nat->Q*tape)
  (x_init: nat*nat*nat)
  (calc_step: nat*nat*nat->option (nat*nat*nat)).

Definition Cert_WF(tm:string)(cert:Cert):Prop :=
match cert with
| cert1 S0_ x_init calc_step =>
  forall T,
  (check_halt calc_step x_init T = true ->
  halts (TM_from_str tm) c0)
end.

Ltac solve_Cert_WF :=
match goal with
| |- Cert_WF ?s (cert1 ?S0' ?x_init ?calc_step) =>
  unfold Cert_WF;
  remember (TM_from_str s) as tm eqn:Heqtm;
  compute in Heqtm;
  subst tm;
  eapply halt with (S0:=S0');
  [ unfold config;
    solve_rule
  | solve_rule
  | intros x;
    destruct x as [[a b] c];
    unfold config;
    solve_calc_step_spec
  ]
end.

Lemma WF1:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_1RD0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then Some (2+a,c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF2:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_1RD0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then Some (2+a,c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF3:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RA1RE_0RF0RB_---1LC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (2+a,1+c,0)%nat
      end
    ) else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF4:
  Cert_WF "1RB1LA_1RC1RE_1RD0LA_1LC1RD_1RF0RD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)%nat
      | S (S (S c)) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF5:
  Cert_WF "1RB1LA_1RC1RE_1LD0LA_1LC1RD_1RF0RD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)%nat
      | S (S (S c)) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF6:
  Cert_WF "1RB1LA_1RC1RE_1LD0LA_1LC1RD_0RF0RD_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)%nat
      | S (S (S c)) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S c => Some (1,1+a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF7:
  Cert_WF "1LB0RB_1LC1RB_1RC0LD_1RE1LD_1RF1RA_---0RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a,c)%nat else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)%nat
      | S (S (S O)) => Some (3,1+a,1)%nat
      | S (S (S (S c))) => Some (4+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF8:
  Cert_WF "1RB1LA_1RC1RC_1RD0RD_1LE1RD_1RF0LA_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S c => Some (3,a,1+c)%nat
      end
    ) else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S O => None
      | S (S c) => Some (2+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF9:
  Cert_WF "1RB1LA_1RC1RC_1LD0RD_1LE1RD_1RF0LA_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S c => Some (3,a,1+c)%nat
      end
    ) else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => Some (1,1+a,1)%nat
      | S O => None
      | S (S c) => Some (2+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF10:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1LA0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a,c)%nat else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)%nat
      | S (S (S O)) => Some (3,1+a,1)%nat
      | S (S (S (S c))) => Some (4+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF11:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a,c)%nat else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)%nat
      | S (S (S O)) => Some (3,1+a,1)%nat
      | S (S (S (S c))) => Some (4+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF12:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (1,2+a,c)%nat else
    if b =? 1 then Some (1,1+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)%nat
      | S (S (S O)) => Some (3,1+a,1)%nat
      | S (S (S (S c))) => Some (4+a,c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF13:
  Cert_WF "1RB0LD_1LC1RE_1LA1RC_1RB1LD_1RF0RC_---0LD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF14:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then Some (1,a+c,1)%nat else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF15:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then Some (1,a+c,1)%nat else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF16:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_1RB0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then Some (1,a+c,1)%nat else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF17:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then Some (1,a+c,1)%nat else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF18:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then Some (1,a+c,1)%nat else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF19:
  Cert_WF "1RB1LA_1RC1RD_1LA1RE_1RF0RC_1LF1RE_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match c with  
      | O => Some (1,2+a,0)%nat
      | S c => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF20:
  Cert_WF "1RB1LA_1LC1RF_1LA1RD_1LE1RD_---0LA_1RE0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF21:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF22:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF23:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF24:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then (
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)%nat
      end
    ) else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (1,2+a,c)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O => None
      | S a => Some (1,1+a+c,1)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF25:
  Cert_WF "1LB1RD_1RC0LC_1RA1LC_1RF0RE_1LB1RE_---1RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{A}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (0,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S c => Some (3+a,c,0)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)%nat
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF26:
  Cert_WF "1RB0LB_1RC1LB_0LD1RE_1LA1RD_1RF0RD_---0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{C}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (2,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,2)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O => Some (3,1+c,1)%nat
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF27:
  Cert_WF "1RB0LB_1RC1LB_1LA1RD_1RE0RF_---0RB_1LA1RF"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{C}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (2,0,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,2)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)%nat
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF28:
  Cert_WF "1LB1RA_1LC0LC_1RD1LC_1LB1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,2,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,1)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)%nat
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF29:
  Cert_WF "1LB1RA_1LC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,2,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,1)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O => Some (3,1+c,1)%nat
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF30:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_1LB1RE_0RF0RA_---0LB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,2,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,1)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)%nat
        | S c => Some (3,c,1)%nat
        end
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF31:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,2,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,1)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O => Some (3,1+c,1)%nat
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF32:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_0LA1RE_0RF0RA_---0LB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (1,2,0)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (3,a+c,1)%nat else
    if b =? 1 then (
      match c with
      | O => None
      | S O => Some (1,2+a,1)%nat
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)%nat
      | S (S (S (S c))) => Some (5+a,c,1)%nat
      end
    ) else
    if b =? 0 then (
      match a with
      | O => Some (3,1+c,1)%nat
      | S a => Some (1,a,1+c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF33:
  Cert_WF "1RB1LA_1RC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (2,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (2,1+a+c,1)%nat else
    if b =? 1 then Some (2+a,c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (2,a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF34:
  Cert_WF "1RB1LA_1LC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (2,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (2,1+a+c,1)%nat else
    if b =? 1 then Some (2+a,c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (2,a,c)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF35:
  Cert_WF "1RB1LA_0RC1RE_1LD0LA_0LA---_1RC0RF_1LA0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (0,0,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (0,3+a+c,1)%nat else
    if b =? 1 then Some (2+a,c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c =>
        match a with
        | O => Some (2,c,2)%nat
        | S a => Some (2,a,1+c)%nat
        end
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF36:
  Cert_WF "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_1RE0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{F}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (0,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (0,1+a,2+c)%nat else
    if b =? 1 then Some (0,3+a+c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (2+a,c,0)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF37:
  Cert_WF "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_0RD0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{F}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (0,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (0,1+a,2+c)%nat else
    if b =? 1 then Some (0,3+a+c,0)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (2+a,c,0)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF38:
  Cert_WF "1LB1LE_1LC1RB_1RB0LD_0RA1LD_1RF0RB_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)
    (0,1,1)%nat
    (fun x =>
    let '(a,b,c) := x in
    if b =? 2 then Some (0,a,3+c)%nat else
    if b =? 1 then Some (0,2+a+c,1)%nat else
    if b =? 0 then (
      match c with
      | O => None
      | S c => Some (2+a,c,0)%nat
      end
    ) else
    Some (a,b,c))
  ).
Proof.
  solve_Cert_WF.
Qed.


