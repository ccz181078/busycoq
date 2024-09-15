
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.

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

Ltac simpl_tape' :=
  simpl_tape; repeat rewrite lpow_mul; cbn.

Ltac solve_rule:=
  match goal with
  | |- forall _, _ => intros; solve_rule
  | |- (c0 -[ _ ]->* ?S0 _ _ _) => unfold S0; solve_init
  | |- (?S0 _ _ _ -[ _ ]->* ?S0 _ _ _) => unfold S0; simpl_tape'; execute_with_shift_rule
  | |- (halts _ (?S0 _ _ _)) => unfold S0; simpl_tape'; solve_halt
  | |- (c0 -[ _ ]->* _) => solve_init
  | |- (_ -[ _ ]->* _) => simpl_tape'; execute_with_shift_rule
  | |- (halts _ _) => simpl_tape'; solve_halt
  end.



Lemma CapIncs(tm:TM)(cfg:nat*nat*nat->Q*tape) ca cb cc:
  (forall a b c, cfg (ca+a,b,cc+c) -[tm]->* cfg (a,cb+b,c)) ->
  (forall a b c, cfg (a,b,c) -[tm]->*
  let x:=min (a/ca) (c/cc) in
  cfg (
    a-x*ca,
    b+x*cb,
    c-x*cc)%nat
  ).
Proof.
  intros H a b c.
  cbn.
  remember (min (a/ca) (c/cc)) as x.
  assert (x*ca<=a) as H0. {
    rewrite Heqx.
    rewrite <-Nat.mul_min_distr_r.
    rewrite Nat.min_le_iff.
    left.
    rewrite Nat.mul_comm.
    apply Nat.Div0.mul_div_le.
  }
  assert (x*cc<=c) as H1. {
    rewrite Heqx.
    rewrite <-Nat.mul_min_distr_r.
    rewrite Nat.min_le_iff.
    right.
    rewrite Nat.mul_comm.
    apply Nat.Div0.mul_div_le.
  }
  remember (a-x*ca) as a0.
  remember (c-x*cc) as c0.
  replace a with (x*ca+a0) by lia.
  replace c with (x*cc+c0) by lia.
  clear Heqa0 Heqc0 H0 H1 Heqx a c.
  gen a0 b c0.
  induction x; intros.
  1: finish.
  cbn.
  repeat rewrite <-Nat.add_assoc.
  follow H.
  follow IHx.
  finish.
Qed.

Open Scope list.

Section CubicCap.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Hypothesis S0: nat->nat->nat->Q*tape.

Definition config(x:nat*nat*nat):=
  let '(a,b,c) := x in S0 a b c.

Hypothesis x_init: nat*nat*nat.

Hypothesis bouncer_rule: nat*nat*nat->nat*nat*nat.

Hypothesis calc_step: nat*nat*nat->option (nat*nat*nat).

Hypothesis init: c0 -->* config x_init.

Hypothesis bouncer_rule_spec:
  forall x, config x -->* config (bouncer_rule x).

Hypothesis calc_step_spec:
  forall x,
  match calc_step x with
  | Some y => config x -->* config y
  | None => halts tm (config x)
  end.

Fixpoint check_halt(x:nat*nat*nat)(T:nat):bool :=
match T with
| O => false
| S T0 =>
  match (calc_step (bouncer_rule x)) with
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
    pose proof (calc_step_spec (bouncer_rule x)) as H0.
    destruct (calc_step (bouncer_rule x)) eqn:E.
    + specialize (IHT p H).
      apply (halts_evstep _ _ _ IHT).
      follow (bouncer_rule_spec x).
      apply H0.
    + apply (halts_evstep _ _ _ H0).
      apply bouncer_rule_spec.
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

End CubicCap.

Lemma divmod_spec a b:
  a = (a mod b) + (a/b)*b.
Proof.
  pose proof (Nat.Div0.div_mod a b) as H.
  lia.
Qed.


Ltac solve_calc_step_spec :=
  match goal with
  | |- match (if (?x =? ?x0)%nat then _ else _) with _ => _ end =>
    destruct (Nat.eqb_spec x x0); subst;
    solve_calc_step_spec
  | |- match (match ?x mod ?y with _ => _ end) with _ => _ end =>
    pose proof (divmod_spec x y) as H;
    remember (x/y) as x' eqn:Heqx';
    remember (x mod y) as x'' eqn:Heqx'';
    subst x;
    clear Heqx' Heqx'';
    solve_calc_step_spec
  | |- match (match ?x with _ => _ end) with _ => _ end =>
    destruct x;
    solve_calc_step_spec
  | _ => try solve_rule
  end.

Inductive Cert :=
| cert1
  (S0: nat->nat->nat->Q*tape)
  (x_init: nat*nat*nat)
  (bouncer_rule: nat*nat*nat->nat*nat*nat)
  (calc_step: nat*nat*nat->option (nat*nat*nat)).

Definition Cert_WF(tm:string)(cert:Cert):Prop :=
match cert with
| cert1 S0_ x_init bouncer_rule calc_step =>
  forall T,
  (check_halt bouncer_rule calc_step x_init T = true ->
  halts (TM_from_str tm) c0)
end.

Ltac solve_Cert_WF :=
match goal with
| |- Cert_WF ?s (cert1 ?S0' ?x_init ?bouncer_rule ?calc_step) =>
  unfold Cert_WF;
(*
  remember (TM_from_str s) as tm eqn:Heqtm;
  compute in Heqtm;
  subst tm;
*)
  eapply halt with (S0:=S0');
  [ unfold config;
    solve_rule
  | intros x;
    destruct x as [[a b] c];
    eapply CapIncs;
    unfold config;
    solve_rule
  | intros x;
    destruct x as [[a b] c];
    unfold config;
    solve_calc_step_spec
  ]
end.

Close Scope sym.


Lemma WF1:
  Cert_WF "1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_---1LE"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{B}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (0,0,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,0,4)
      | 1 => Some (b*2,0,4)
      | S (S c) => Some (1+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF2:
  Cert_WF "1RB1LF_1LC1LE_1RD1LB_---1RC_1RA1RF_0LB0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF3:
  Cert_WF "1RB1RE_0LC1RA_---1LD_0LE1RD_0RA1LF_1LC0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{A}} [0] *> [1;0]^^b *> [1;1;0;1]^^(1+c) *> const 0)%sym
    (3,2,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*3,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (2+b*2,2,0)
      | S c => Some (4+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 => Some (4+b*2,2,0)
      | 1 => Some (5+b*2,2,0)
      | S (S c) => Some (7+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (1,2,b)
          end
        | 1 =>
          match b/2 with
          | b => None
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (1,2,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (5,2,b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (2+a,2,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (a,2,1+b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF4:
  Cert_WF "1RB1LE_1LC1LE_1RD1LB_---1RC_0LB1RF_0RA0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF5:
  Cert_WF "1RB1LF_1LC1LE_1RD1LB_---1RC_0RA1RF_0LB0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF6:
  Cert_WF "1RB1LD_1LC1LD_1RD1LB_0LB1RE_1RF0RA_---1RC"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (1,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (4+b*4,0,0)
          end
        | 1 =>
          match b/2 with
          | b => None
          end
        | _ => Some x
        end
      | 1 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (3+b*4,0,1)
          end
        | 1 =>
          match b/2 with
          | b => Some (4+b*4,0,4)
          end
        | _ => Some x
        end
      | S (S c) =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (3+b*4,0,2+c)
          end
        | 1 =>
          match b/2 with
          | b => Some (5+b*4,1,c)
          end
        | _ => Some x
        end
      end
    | 1 =>
      match c with
      | 0 => Some (1,1,2+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF7:
  Cert_WF "1RB1LE_1LC1LE_1RD1LB_---1RC_0LB1RF_---0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF8:
  Cert_WF "1RB1LE_1LC1LE_1RD1LB_---0LE_0LB1RF_1RC0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF9:
  Cert_WF "1RB0RF_1LC1LE_1RD1LB_---1RC_0LB1RA_1RB1LE"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF10:
  Cert_WF "1RB1LF_1LC1LE_1RD1LB_---1RC_0LB1RF_0LB0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF11:
  Cert_WF "1RB1LF_1LC1LE_1RD1LB_---1RC_0LB1RF_0RB0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF12:
  Cert_WF "1LB1LC_0RC0RA_0LD1RB_1LE1LC_1RF1LD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{C}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF13:
  Cert_WF "1RB1LD_0LC1RA_1LA1LB_1LE1RE_---0RF_1RC1LB"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{B}} [1;0]^^b *> [1;1;1;0]^^(c) *> const 0)%sym
    (0,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*3,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (2+b*2,1,0)
      | S c => Some (3+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (1,1,0)
          | S b => None
          end
        | 1 =>
          match b/2 with
          | b => Some (3,2,b)
          end
        | _ => Some x
        end
      | 1 => Some (4+b*2,1,1)
      | S (S c) => Some (4+b*2,4,c)
      end
    | S (S a) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (2+a,1,0)
          | S b => Some (a,2,1+b)
          end
        | 1 =>
          match b/2 with
          | b => Some (a,1,1+b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF14:
  Cert_WF "1LB1LC_1RC1LD_0LA1RB_1LE1RE_---0RF_1RA1LC"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{C}} [1;0]^^b *> [1;1;1;0]^^(c) *> const 0)%sym
    (2,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*3,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (2+b*2,1,0)
      | S c => Some (3+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (1,1,0)
          | S b => None
          end
        | 1 =>
          match b/2 with
          | b => Some (3,2,b)
          end
        | _ => Some x
        end
      | 1 => Some (4+b*2,1,1)
      | S (S c) => Some (4+b*2,4,c)
      end
    | S (S a) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (2+a,1,0)
          | S b => Some (a,2,1+b)
          end
        | 1 =>
          match b/2 with
          | b => Some (a,1,1+b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF15:
  Cert_WF "1LB1LD_0RC0RA_1LA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,0)
      | S c => Some (2+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,0)
      | S (S c) => Some (4+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 => Some (2,1,b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF16:
  Cert_WF "1LB1RE_1LC1LA_0RD0RB_1RE1RD_1LF0RA_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (0,1,1)
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (1+b*2,2,1)
      | 2 => Some (2+b*2,2,1)
      | S (S (S c)) => Some (4+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (0,2,1)
        | S b => Some (2,2,b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF17:
  Cert_WF "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{E}} [0] *> [0;1]^^(b) *> [1]^^(c) *> const 0)%sym
    (3,0,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match b with
      | 0 =>
        match c with
        | 0 => Some x
        | 1 => Some (3,0,4)
        | S (S c) => None
        end
      | 1 =>
        match c with
        | 0 => Some (3,0,4)
        | S c => None
        end
      | S (S b) =>
        match c with
        | 0 => Some (3+b*2,1,1)
        | S c => Some (5+b*2,0,c)
        end
      end
    | 1 =>
      match c with
      | 0 => Some (3,0,4+b*2)
      | 1 => Some (3+b*2,1,1)
      | S (S c) => Some (5+b*2,0,c)
      end
    | 2 =>
      match c with
      | 0 => Some (0,1,3+b*2)
      | S c => Some (0,3+b,c)
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (1+a,1,3+b*2)
      | S c => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF18:
  Cert_WF "1RB1LF_1LC0RA_1RE1LD_1LC1LF_---1RC_0LD1RB"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{F}} [1] *> [0;1]^^(b) *> [1]^^(c) *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF19:
  Cert_WF "1RB1LC_0RC0RA_0LD1RB_1LE1LC_1RF1LD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{C}} [1] *> [0;1]^^(b) *> [1]^^(c) *> const 0)%sym
    (1,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => Some (1,0,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,0,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF20:
  Cert_WF "1LB1LD_0RC0RA_0LA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,0,1)
      | S c => Some (2+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,0,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 => Some (2,0,1+b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF21:
  Cert_WF "1LB1LD_0RC0RA_1RA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,1)
      | 1 => Some (2+b*2,1,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,1)
      | 2 => Some (4+b*2,1,1)
      | S (S (S c)) => Some (6+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,1,1)
        | S b => Some (4,0,1+b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF22:
  Cert_WF "1LB1RE_1LC1LA_0RD0RB_1RB1RD_1LF0RA_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (1,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,1)
      | 1 => Some (2+b*2,1,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,1)
      | 2 => Some (4+b*2,1,1)
      | S (S (S c)) => Some (6+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,1,1)
        | S b => Some (4,0,1+b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF23:
  Cert_WF "1LB0LC_1RC1LA_0RD1RC_1RE1RA_1LF1RC_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,1)
      | 1 => Some (1+b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b with
        | 0 => None
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (1+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF24:
  Cert_WF "1LB0LD_1RC1LA_1LF1RD_0RE1RD_1RC1RA_---0LC"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,1)
      | 1 => Some (1+b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b with
        | 0 => None
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (1+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF25:
  Cert_WF "1LB0LC_1RB1LA_0RD1RC_1RE1RA_1LF1RC_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,1)
      | 1 => Some (1+b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b with
        | 0 => None
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (1+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF26:
  Cert_WF "1LB0LC_0LC1LA_0RD1RC_1RE1RA_1LF1RC_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,1)
      | 1 => Some (1+b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b with
        | 0 => None
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (1+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF27:
  Cert_WF "1LB1RD_1RC1RD_1LD1RB_0RB1LE_1LF0LA_---0LC"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{A}} [0] *> [1;0]^^b *> [1;1;1;0]^^(c) *> const 0)%sym
    (0,2,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*3,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,0)
      | S c => Some (4+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (8,1,0)
          | S b => Some (5,3,b)
          end
        | 1 =>
          match b/2 with
          | b => None
          end
        | _ => Some x
        end
      | 1 => Some (8+b*2,1,0)
      | S (S c) => Some (5+b*2,3,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (3,1,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (3,3,b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (4+a,1,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (a,2,1+b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF28:
  Cert_WF "1RB0LB_1LC0LF_0LE1RD_1LE0RC_1LA1LD_---1RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (1,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,2,0)
      | 1 => Some (2+b*2,2,0)
      | S (S c) => Some (3+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b with
        | 0 => None
        | S b => Some (1,2,1+b)
        end
      | 1 => Some (3+b*2,2,0)
      | 2 => Some (4+b*2,2,0)
      | S (S (S c)) => Some (5+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 => Some (1,2,1+b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (1+a,2,b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF29:
  Cert_WF "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{B}} [0;1]^^(b) *> [1]^^(2+c) *> const 0)%sym
    (4,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match b mod 2 with
      | 0 =>
        match b/2 with
        | b => Some (1+b*4,1,c)
        end
      | 1 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (1+b*4,1,4)
          | 1 => None
          | S (S c) => Some (3+b*4,2,c)
          end
        end
      | _ => Some x
      end
    | 1 =>
      match c with
      | 0 => Some (1,1,4+b*2)
      | _ => Some x
      end
    | S (S a) =>
      match c with
      | 0 => Some (a,1,4+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF30:
  Cert_WF "1LB---_0LC0LA_1RD0RE_1LE1RD_1LA1LF_1RF0RC"
  (cert1
    (fun a b c => const 0 <* [1;0]^^(a) <{{F}} [1;1] *> [1;1;1;1]^^(b) *> [1;0]^^(c) *> [1;1;1;1] *> const 0)%sym
    (0,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/1) (c/1) in
    (a-i*1,b+i*1,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (0,1+b,0)
      | 1 => None
      | S (S c) => Some (3+b*2,0,c)
      end
    | S a =>
      match c with
      | 0 =>
        match a mod 2 with
        | 0 =>
          match a/2 with
          | a => Some (0,a,3+b*2)
          end
        | 1 =>
          match a/2 with
          | a => Some (4+a*2,0,1+b*2)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF31:
  Cert_WF "1LB1LD_0RC1LA_1LA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,0)
      | 1 => Some (2+b*2,1,0)
      | S (S c) => Some (2+b*2,1,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,0)
      | S (S c) => Some (4+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 => Some (2,1,b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (4,1,b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF32:
  Cert_WF "1LB1LD_0RC1LA_1LA1RC_0LB1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,0)
      | 1 => Some (2+b*2,1,0)
      | S (S c) => Some (2+b*2,1,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,0)
      | S (S c) => Some (4+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 => Some (2,1,b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (4,1,b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF33:
  Cert_WF "1LB1RE_1LC1LA_0RD1LB_1RE1RD_1LF0RA_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (2,2,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,2,1)
        | S b => Some (1+b*2,2,1)
        end
      | 1 => Some (b*2,2,1)
      | S (S c) => Some (2+b*2,2,c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (1+b*2,2,1)
      | 2 => Some (2+b*2,2,1)
      | S (S (S c)) => Some (4+b*2,2,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (0,2,1)
        | S b => Some (2,2,b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,2,1)
        | S b => Some (4,2,b)
        end
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF34:
  Cert_WF "1LB1RE_1LC1LA_0RD1LB_1RB1RD_1LF0RA_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (1,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,1)
      | 1 => Some (2+b*2,1,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,1)
      | 2 => Some (4+b*2,1,1)
      | S (S (S c)) => Some (6+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,1,1)
        | S b => Some (4,0,1+b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (4,1,1)
        | S b => Some (6,0,1+b)
        end
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF35:
  Cert_WF "1LB1LD_0RC1LA_1RA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,1,1)
      | 1 => Some (2+b*2,1,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,1,1)
      | 2 => Some (4+b*2,1,1)
      | S (S (S c)) => Some (6+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (2,1,1)
        | S b => Some (4,0,1+b)
        end
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 =>
        match b with
        | 0 => Some (4,1,1)
        | S b => Some (6,0,1+b)
        end
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF36:
  Cert_WF "1LB1LD_0RC1LA_0LA1RC_1LA1RE_1LF0RD_---0LE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (0,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (1+b*2,0,1)
      | S c => Some (2+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (3+b*2,0,1)
      | S (S c) => Some (4+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 => Some (2,0,1+b)
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (4,0,1+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (a,2,1+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF37:
  Cert_WF "1RB0LE_1LC1RA_1RA1LD_0LC0LA_1RE1RF_0RC---"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{E}} [0;0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (1,0,3)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match b with
      | 0 =>
        match c with
        | 0 => Some (2,0,3)
        | S c => None
        end
      | S b => Some (1,1+b,c)
      end
    | 1 =>
      match c with
      | 0 => Some (0,1,5+b*2)
      | 1 => Some (5+b*2,0,1)
      | 2 => Some (5+b*2,0,3)
      | S (S (S c)) => Some (4+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 => Some (0,0,5+b*2)
      | S c => Some (0,3+b,c)
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (1+a,0,5+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF38:
  Cert_WF "1RB1LD_1RC0LE_1LA1RB_0LA0LB_1RE1RF_0RA---"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{E}} [0;0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (0,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match b with
      | 0 =>
        match c with
        | 0 => Some (2,0,3)
        | S c => None
        end
      | S b => Some (1,1+b,c)
      end
    | 1 =>
      match c with
      | 0 => Some (0,1,5+b*2)
      | 1 => Some (5+b*2,0,1)
      | 2 => Some (5+b*2,0,3)
      | S (S (S c)) => Some (4+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 => Some (0,0,5+b*2)
      | S c => Some (0,3+b,c)
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (1+a,0,5+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF39:
  Cert_WF "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RA_---1RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (3,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (3,0,3+b*2)
      | S c => Some (2,1+b,c)
      end
    | 1 =>
      match b mod 2 with
      | 0 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,2+b*4)
          | 1 => Some (4+b*4,0,1)
          | 2 => Some (4+b*4,0,3)
          | S (S (S c)) => Some (3+b*4,1,c)
          end
        end
      | 1 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,4+b*4)
          | 1 => None
          | 2 => Some (7+b*4,0,1)
          | 3 => Some (7+b*4,0,3)
          | S (S (S (S c))) => Some (6+b*4,1,c)
          end
        end
      | _ => Some x
      end
    | 2 =>
      match b mod 2 with
      | 0 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,4+b*4)
          | 1 => None
          | 2 => Some (7+b*4,0,1)
          | 3 => Some (7+b*4,0,3)
          | S (S (S (S c))) => Some (6+b*4,1,c)
          end
        end
      | 1 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,6+b*4)
          | 1 => Some (8+b*4,0,1)
          | 2 => Some (8+b*4,0,3)
          | S (S (S c)) => Some (7+b*4,1,c)
          end
        end
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (1+a,0,5+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF40:
  Cert_WF "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RA_---1LB"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (3,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (3,0,3+b*2)
      | S c => Some (2,1+b,c)
      end
    | 1 =>
      match b mod 2 with
      | 0 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,2+b*4)
          | 1 => Some (4+b*4,0,1)
          | 2 => Some (4+b*4,0,3)
          | S (S (S c)) => Some (3+b*4,1,c)
          end
        end
      | 1 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,4+b*4)
          | 1 => None
          | 2 => Some (7+b*4,0,1)
          | 3 => Some (7+b*4,0,3)
          | S (S (S (S c))) => Some (6+b*4,1,c)
          end
        end
      | _ => Some x
      end
    | 2 =>
      match b mod 2 with
      | 0 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,4+b*4)
          | 1 => None
          | 2 => Some (7+b*4,0,1)
          | 3 => Some (7+b*4,0,3)
          | S (S (S (S c))) => Some (6+b*4,1,c)
          end
        end
      | 1 =>
        match b/2 with
        | b =>
          match c with
          | 0 => Some (2,1,6+b*4)
          | 1 => Some (8+b*4,0,1)
          | 2 => Some (8+b*4,0,3)
          | S (S (S c)) => Some (7+b*4,1,c)
          end
        end
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (1+a,0,5+b*2)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF41:
  Cert_WF "1LB1LE_0LC0LD_1RD1LB_1RE0RC_1LF1RD_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{D}} [0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (0,1,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match b with
      | 0 => Some (1,1,1+c)
      | S b =>
        match c with
        | 0 => Some (6+b*2,1,1)
        | 1 => Some (5+b*2,1,4)
        | S (S c) => Some (7+b*2,1,c)
        end
      end
    | 1 =>
      match c with
      | 0 =>
        match b mod 3 with
        | 0 =>
          match b/3 with
          | b => Some (1,1,3+b*6)
          end
        | 1 =>
          match b/3 with
          | b => Some (1,1,6+b*6)
          end
        | 2 =>
          match b/3 with
          | b => None
          end
        | _ => Some x
        end
      | 1 => Some (2+b*2,1,1)
      | 2 => Some (1+b*2,1,4)
      | S (S (S c)) => Some (3+b*2,1,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b mod 3 with
        | 0 =>
          match b/3 with
          | b => Some (1,1,6+b*6)
          end
        | 1 =>
          match b/3 with
          | b => None
          end
        | 2 =>
          match b/3 with
          | b => Some (1,1,9+b*6)
          end
        | _ => Some x
        end
      | 1 => Some (4+b*2,1,1)
      | 2 => Some (3+b*2,1,4)
      | S (S (S c)) => Some (5+b*2,1,c)
      end
    | 3 =>
      match c with
      | 0 =>
        match b mod 3 with
        | 0 =>
          match b/3 with
          | b => Some (1,0,5+b*6)
          end
        | 1 =>
          match b/3 with
          | b => Some (3,1,5+b*6)
          end
        | 2 =>
          match b/3 with
          | b => None
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | 4 =>
      match c with
      | 0 =>
        match b mod 3 with
        | 0 =>
          match b/3 with
          | b => Some (2,0,5+b*6)
          end
        | 1 =>
          match b/3 with
          | b => Some (0,1,7+b*6)
          end
        | 2 =>
          match b/3 with
          | b => Some (3,1,8+b*6)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | S (S (S (S (S a)))) =>
      match c with
      | 0 =>
        match b mod 3 with
        | 0 =>
          match b/3 with
          | b => Some (3+a,0,5+b*6)
          end
        | 1 =>
          match b/3 with
          | b => Some (1+a,1,7+b*6)
          end
        | 2 =>
          match b/3 with
          | b => Some (a,1,10+b*6)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF42:
  Cert_WF "1RB1LF_1LC0RA_0RD1LB_---1RE_1RD1RB_0LA0LB"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{B}} [0] *> [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym
    (0,1,3)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/3) (c/1) in
    (a-i*3,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => None
      | 1 => Some (b*2,1,1)
      | 2 => Some (b*2,1,3)
      | S (S (S c)) => Some (2+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 => Some (0,1,1+b*2)
      | S c => Some (0,2+b,c)
      end
    | 2 =>
      match c with
      | 0 => Some (0,1,3+b*2)
      | S c => Some (0,3+b,c)
      end
    | 3 =>
      match c with
      | 0 => Some (0,1,5+b*2)
      | S c => Some x
      end
    | 4 =>
      match c with
      | 0 => Some (0,2,5+b*2)
      | S c => Some x
      end
    | S (S (S (S (S a)))) =>
      match c with
      | 0 => Some (a,1,5+b*2)
      | S c => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF43:
  Cert_WF "1LB0RC_1LC1LA_1RD1RA_1LF1RE_0LB1RE_---0LD"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (2,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (2+b*2,0,1)
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (4+b*2,0,1)
      | S (S c) => Some (5+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 => Some (a,0,3+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF44:
  Cert_WF "1LB0RC_1LC1LA_1RD1RA_1LF1LE_0LB1RE_---0LD"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (2,0,1)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (2+b*2,0,1)
      | S c => Some (3+b*2,0,1+c)
      end
    | 1 =>
      match c with
      | 0 => None
      | 1 => Some (4+b*2,0,1)
      | S (S c) => Some (5+b*2,0,1+c)
      end
    | 2 =>
      match c with
      | 0 => None
      | _ => Some x
      end
    | 3 =>
      match c with
      | 0 => Some (1,0,4+b)
      | _ => Some x
      end
    | S (S (S (S a))) =>
      match c with
      | 0 => Some (1+a,0,3+b)
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF45:
  Cert_WF "1RB0LB_1LC1RA_---0LD_1LA1LE_1LD0RF_1RD1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^(a) <{{E}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym
    (3,0,2)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*2,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 => Some (1+c*2+b*2,0,2)
    | 1 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => None
          end
        | 1 =>
          match b/2 with
          | b => Some (5+b*4,0,2)
          end
        | _ => Some x
        end
      | S c => Some (3+c*2+b*2,0,2)
      end
    | 2 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (5+b*4,0,2)
          end
        | 1 =>
          match b/2 with
          | b => None
          end
        | _ => Some x
        end
      | S c => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (a,0,3+b*2)
          end
        | 1 =>
          match b/2 with
          | b => Some (6+b*4+a,0,2)
          end
        | _ => Some x
        end
      | S c => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.



Lemma WF46:
  Cert_WF "1LB1RC_0RC1LD_1RA1RB_1LE0LF_---0LA_1LC1RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a <{{F}} [0] *> [1;0]^^b *> [1;1;1;0]^^(c) *> const 0)%sym
    (8,1,0)
    (fun x =>
    let '(a,b,c) := x in
    let i:=min (a/2) (c/1) in
    (a-i*2,b+i*3,c-i*1))
    (fun x =>
    let '(a,b,c) := x in
    match a with
    | 0 =>
      match c with
      | 0 => Some (b*2,2,0)
      | S c => Some (4+b*2,1,c)
      end
    | 1 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | 0 => Some (8,1,0)
          | S b => Some (5,3,b)
          end
        | 1 =>
          match b/2 with
          | b => None
          end
        | _ => Some x
        end
      | 1 => Some (8+b*2,1,0)
      | S (S c) => Some (5+b*2,3,c)
      end
    | 2 =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (3,1,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (3,3,b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    | S (S (S a)) =>
      match c with
      | 0 =>
        match b mod 2 with
        | 0 =>
          match b/2 with
          | b => Some (4+a,1,b)
          end
        | 1 =>
          match b/2 with
          | b => Some (a,2,1+b)
          end
        | _ => Some x
        end
      | _ => Some x
      end
    end)
  ).
Proof.
  solve_Cert_WF.
Qed.
