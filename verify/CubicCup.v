
From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import CubicCap.
From BusyCoq Require Import UintArith.
Import UintArith.N'.

Definition cup_rule :=
  (fun '(a,b,c) =>
  (b/3*2+a,b mod 3,b/3*1+c)).

Definition cup_rule' :=
  (fun '(a,b,c) =>
  (b/3+b/3+a,b mod 3,b/3+c))%N'.


Lemma CupIncs(tm:TM)(cfg:nat*nat*nat->Q*tape) ca cb cc:
  (forall a b c, cfg (a,cb+b,c) -[tm]->* cfg (ca+a,b,cc+c)) ->
  (forall a b c, cfg (a,b,c) -[tm]->*
  cfg (
    b/cb*ca+a,
    b mod cb,
    b/cb*cc+c)%nat
  ).
Proof.
  intros H a b c.
  pose proof (Nat.Div0.div_mod b cb) as H0.
  remember (b / cb) as b0.
  remember (b mod cb) as b1.
  clear Heqb0 Heqb1.
  subst b.
  rewrite (Nat.mul_comm cb b0).
  gen a c.
  induction b0; intros.
  - finish.
  - cbn[Nat.mul].
    rewrite <-Nat.add_assoc.
    follow H.
    follow IHb0.
    finish.
Qed.


Ltac solve_calc_step_spec :=
  match goal with
  | |- match (if (?x =? ?x0)%nat then _ else _) with _ => _ end =>
    destruct (Nat.eqb_spec x x0); subst;
    solve_calc_step_spec
  | |- match (match ?x mod ?y with _ => _ end) with _ => _ end =>
    pose proof (divmod_spec x y);
    remember (x/y) eqn:Heqx';
    remember (x mod y) eqn:Heqx'';
    subst x;
    clear Heqx' Heqx'';
    solve_calc_step_spec
  | |- match (match ?x with _ => _ end) with _ => _ end =>
    destruct x;
    solve_calc_step_spec
  | _ => try solve_rule
  end.

Ltac solve_Cert_WF :=
time
match goal with
| |- Cert_WF ?s (cert1 ?S0' ?x_init ?bouncer_rule0 ?bouncer_rule' ?calc_step0 ?calc_step') =>
  unfold Cert_WF;
  idtac s;
  eapply calc_steps'_spec with (S0:=S0') (bouncer_rule:=bouncer_rule0) (calc_step:=calc_step0);
  [ unfold config;
    solve_rule
  | unfold cup_rule,cup_rule';
    intros x;
    destruct x as [[a b] c];
    eapply CupIncs;
    unfold config;
    solve_rule
  | unfold cup_rule,cup_rule';
    try (solve_nat_N'_eq; fail)
  | intros x;
    destruct x as [[a b] c];
    unfold config;
    solve_calc_step_spec
  | try (solve_nat_N'_eq; fail)
  ]
end.


Lemma WF1:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_1RD0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (1,1+a,c)
      end
    | 1 => Some (2+a,c,0)
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None => Some (2+a,c,0)
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF2:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_0RC0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (1,1+a,c)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (2+a,1+c,0)
      end
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,1+c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF3:
  Cert_WF "1RB0LC_1LA1RB_1RD1LC_1RA1RE_0RF0RB_---1LC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S c => Some (1,1+a,c)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (2+a,1+c,0)
      end
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,1+c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF4:
  Cert_WF "1RB1LA_1RC1RE_1RD0LA_1LC1RD_1RF0RD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S c => Some (1,1+a,c)
      end
    | 1 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)
      | S (S (S c)) => Some (4+a,c,1)
      end
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,4+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF5:
  Cert_WF "1RB1LA_1RC1RE_1LD0LA_1LC1RD_1RF0RD_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S c => Some (1,1+a,c)
      end
    | 1 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)
      | S (S (S c)) => Some (4+a,c,1)
      end
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,4+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF6:
  Cert_WF "1RB1LA_1RC1RE_1LD0LA_1LC1RD_0RF0RD_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S c => Some (1,1+a,c)
      end
    | 1 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (1,4+a,1)
      | S (S (S c)) => Some (4+a,c,1)
      end
    | 2 => Some (1,2+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c => Some (1,1+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,4+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF7:
  Cert_WF "1LB0RB_1LC1RB_1RC0LD_1RE1LD_1RF1RA_---0RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)
      | S (S (S O)) => Some (3,1+a,1)
      | S (S (S (S c))) => Some (4+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 => Some (1,2+a,c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (3,a,2)
      | Some c =>
      match N'OS c with
      | None => Some (3,1+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a,c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF8:
  Cert_WF "1RB1LA_1RC1RC_1RD0RD_1LE1RD_1RF0LA_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S O => None
      | S (S c) => Some (2+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 =>
      match c with
      | O => None
      | S c => Some (3,a,1+c)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,c,1)
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (3,a,1+c)
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF9:
  Cert_WF "1RB1LA_1RC1RC_1LD0RD_1LE1RD_1RF0LA_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => Some (1,1+a,1)
      | S O => None
      | S (S c) => Some (2+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 =>
      match c with
      | O => None
      | S c => Some (3,a,1+c)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => Some (1,1+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,c,1)
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (3,a,1+c)
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF10:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1LA0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)
      | S (S (S O)) => Some (3,1+a,1)
      | S (S (S (S c))) => Some (4+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 => Some (1,2+a,c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (3,a,2)
      | Some c =>
      match N'OS c with
      | None => Some (3,1+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a,c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF11:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)
      | S (S (S O)) => Some (3,1+a,1)
      | S (S (S (S c))) => Some (4+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 => Some (1,2+a,c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (3,a,2)
      | Some c =>
      match N'OS c with
      | None => Some (3,1+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a,c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF12:
  Cert_WF "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S O => None
      | S (S O) => Some (3,a,2)
      | S (S (S O)) => Some (3,1+a,1)
      | S (S (S (S c))) => Some (4+a,c,1)
      end
    | 1 => Some (1,1+a+c,1)
    | 2 => Some (1,2+a,c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (3,a,2)
      | Some c =>
      match N'OS c with
      | None => Some (3,1+a,1)
      | Some c => Some (4+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None => Some (1,1+a+c,1)
    | Some b =>
    match N'OS b with
    | None => Some (1,2+a,c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF13:
  Cert_WF "1RB0LD_1LC1RE_1LA1RC_1RB1LD_1RF0RC_---0LD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (a,b,c)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF14:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => Some (1,a+c,1)
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => Some (1,a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF15:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => Some (1,a+c,1)
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => Some (1,a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF16:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_1RB0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => Some (1,a+c,1)
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => Some (1,a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF17:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => Some (1,a+c,1)
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => Some (1,a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF18:
  Cert_WF "1RB1LA_1RC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => Some (1,a+c,1)
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => Some (1,a+c,1)
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF19:
  Cert_WF "1RB1LA_1RC1RD_1LA1RE_1RF0RC_1LF1RE_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with  
      | O => Some (1,2+a,0)
      | S c => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with  
      | None => Some (1,2+a,0)
      | Some c => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF20:
  Cert_WF "1RB1LA_1LC1RF_1LA1RD_1LE1RD_---0LA_1RE0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (a,b,c)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF21:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (a,b,c)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF22:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (a,b,c)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF23:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (a,b,c)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (a,b,c)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF24:
  Cert_WF "1RB1LA_1LC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{B}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O => None
      | S a => Some (1,1+a+c,1)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (1,2+a,c)
      end
    | 2 =>
      match c with
      | O => None
      | S O => None
      | S (S c) => Some (4+a,c,1)
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None => None
      | Some a => Some (1,1+a+c,1)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (1,2+a,c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => None
      | Some c => Some (4+a,c,1)
      end
      end
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF25:
  Cert_WF "1LB1RD_1RC0LC_1RA1LC_1RF0RE_1LB1RE_---1RA"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{A}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,a,1+c)
      end
    | 1 =>
      match c with
      | O => None
      | S c => Some (3+a,c,0)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (1,2,0)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,a,1+c)
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (3+a,c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF26:
  Cert_WF "1RB0LB_1RC1LB_0LD1RE_1LA1RD_1RF0RD_---0RB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{C}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (2,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O => Some (3,1+c,1)
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,2)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None => Some (3,1+c,1)
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,2)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF27:
  Cert_WF "1RB0LB_1RC1LB_1LA1RD_1RE0RF_---0RB_1LA1RF"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{C}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (2,0,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,2)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (1,2,0)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,2)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF28:
  Cert_WF "1LB1RA_1LC0LC_1RD1LC_1LB1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,2,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,1)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (1,2,0)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF29:
  Cert_WF "1LB1RA_1LC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,2,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O => Some (3,1+c,1)
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,1)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None => Some (3,1+c,1)
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF30:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_1LB1RE_0RF0RA_---0LB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,2,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O =>
        match c with
        | O => Some (1,2,0)
        | S c => Some (3,c,1)
        end
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,1)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None =>
        match N'OS c with
        | None => Some (1,2,0)
        | Some c => Some (3,c,1)
        end
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF31:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,2,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O => Some (3,1+c,1)
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,1)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None => Some (3,1+c,1)
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF32:
  Cert_WF "1LB1RA_1RC0LC_1RD1LC_0LA1RE_0RF0RA_---0LB"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{D}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (1,2,0)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 => 
      match a with
      | O => Some (3,1+c,1)
      | S a => Some (1,a,1+c)
      end
    | 1 => 
      match c with
      | O => None
      | S O => Some (1,2+a,1)
      | S (S O) => None
      | S (S (S O)) => Some (1,6+a,0)
      | S (S (S (S c))) => Some (5+a,c,1)
      end
    | 2 => Some (3,a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None => 
      match N'OS a with
      | None => Some (3,1+c,1)
      | Some a => Some (1,a,1+c)
      end
    | Some b => 
    match N'OS b with
    | None => 
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,2+a,1)
      | Some c =>
      match N'OS c with
      | None => None
      | Some c =>
      match N'OS c with
      | None => Some (1,6+a,0)
      | Some c => Some (5+a,c,1)
      end
      end
      end
      end
    | Some b =>
    match N'OS b with
    | None =>  Some (3,a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF33:
  Cert_WF "1RB1LA_1RC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (2,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (2,a,c)
      end
    | 1 => Some (2+a,c,0)
    | 2 => Some (2,1+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2,a,c)
      end
    | Some b =>
    match N'OS b with
    | None => Some (2+a,c,0)
    | Some b =>
    match N'OS b with
    | None => Some (2,1+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF34:
  Cert_WF "1RB1LA_1LC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (2,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (2,a,c)
      end
    | 1 => Some (2+a,c,0)
    | 2 => Some (2,1+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2,a,c)
      end
    | Some b =>
    match N'OS b with
    | None => Some (2+a,c,0)
    | Some b =>
    match N'OS b with
    | None => Some (2,1+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF35:
  Cert_WF "1RB1LA_0RC1RE_1LD0LA_0LA---_1RC0RF_1LA0RC"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,0,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c =>
        match a with
        | O => Some (2,c,2)
        | S a => Some (2,a,1+c)
        end
      end
    | 1 => Some (2+a,c,0)
    | 2 => Some (0,3+a+c,1)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c =>
        match N'OS a with
        | None => Some (2,c,2)
        | Some a => Some (2,a,1+c)
        end
      end
    | Some b =>
    match N'OS b with
    | None => Some (2+a,c,0)
    | Some b =>
    match N'OS b with
    | None => Some (0,3+a+c,1)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF36:
  Cert_WF "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_1RE0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{F}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (2+a,c,0)
      end
    | 1 => Some (0,3+a+c,0)
    | 2 => Some (0,1+a,2+c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (0,3+a+c,0)
    | Some b =>
    match N'OS b with
    | None => Some (0,1+a,2+c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF37:
  Cert_WF "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_0RD0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{F}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (2+a,c,0)
      end
    | 1 => Some (0,3+a+c,0)
    | 2 => Some (0,1+a,2+c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (0,3+a+c,0)
    | Some b =>
    match N'OS b with
    | None => Some (0,1+a,2+c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF38:
  Cert_WF "1LB1LE_1LC1RB_1RB0LD_0RA1LD_1RF0RB_---1RE"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{E}}> [1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,1,1)
    cup_rule
    cup_rule'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c with
      | O => None
      | S c => Some (2+a,c,0)
      end
    | 1 => Some (0,2+a+c,1)
    | 2 => Some (0,a,3+c)
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS c with
      | None => None
      | Some c => Some (2+a,c,0)
      end
    | Some b =>
    match N'OS b with
    | None => Some (0,2+a+c,1)
    | Some b =>
    match N'OS b with
    | None => Some (0,a,3+c)
    | _ => Some x
    end
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.

Lemma WF39:
  Cert_WF "1LB0LB_1RB0RC_1LD1RC_1LE0LA_0LF0LB_---0RA"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{B}}> [1;1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,1,0)
    (fun '(a, b, c) => (b/2*2+a, b mod 2, b/2*2+c))
    (fun '(a, b, c) => (b/2+b/2+a, b mod 2, b/2+b/2+c))%N'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c mod 2 with
      | 0 =>
        match c/2 with
        | c => Some (1+a,c,0)
        end
      | 1 =>
        match c/2 with
        | 0 =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (2,a,2)
            end
          | 1 =>
            match a/2 with
            | a => None
            end
          | _ => Some x
          end
        | S c => Some (3+a,c,1)
        end
      | _ => Some x
      end
    | 1 =>
      match c mod 2 with
      | 0 =>
        match c/2 with
        | c =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (2,1+a+c,1)
            end
          | 1 =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | _ => Some x
          end
        end
      | 1 =>
        match c/2 with
        | c =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | 1 =>
            match a/2 with
            | a => Some (2,2+a+c,1)
            end
          | _ => Some x
          end
        end
      | _ => Some x
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS (c mod 2) with
      | None =>
        match c/2 with
        | c => Some (1+a,c,0)
        end
      | Some cmod2 =>
      match N'OS (cmod2) with
      | None =>
        match N'OS (c/2) with
        | None =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (2,a,2)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => None
            end
          | _ => Some x
          end
          end
        | Some c => Some (3+a,c,1)
        end
      | _ => Some x
      end
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS (c mod 2) with
      | None =>
        match c/2 with
        | c =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (2,1+a+c,1)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | _ => Some x
          end
          end
        end
      | Some cmod2 =>
      match N'OS (cmod2) with
      | None =>
        match c/2 with
        | c =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => Some (2,2+a+c,1)
            end
          | _ => Some x
          end
          end
        end
      | _ => Some x
      end
      end
    | _ => Some x
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


Lemma WF40:
  Cert_WF "1LB0LB_1RB0RC_1LD1RC_1LE0LA_1LF0LB_---1RB"
  (cert1
    (fun a b c => const 0 <* [1]^^(2+a) {{B}}> [1;1]^^b *> [0] *> [1]^^c *> const 0)%sym
    (0,1,0)
    (fun '(a, b, c) => (b/2*2+a, b mod 2, b/2*2+c))
    (fun '(a, b, c) => (b/2+b/2+a, b mod 2, b/2+b/2+c))%N'
    (fun x =>
    let '(a,b,c) := x in
    match b with
    | 0 =>
      match c mod 2 with
      | 0 =>
        match c/2 with
        | c => Some (1+a,c,0)
        end
      | 1 =>
        match c/2 with
        | 0 =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (2,a,2)
            end
          | 1 =>
            match a/2 with
            | a => None
            end
          | _ => Some x
          end
        | S c => Some (3+a,c,1)
        end
      | _ => Some x
      end
    | 1 =>
      match c mod 2 with
      | 0 =>
        match c/2 with
        | c =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (2,1+a+c,1)
            end
          | 1 =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | _ => Some x
          end
        end
      | 1 =>
        match c/2 with
        | c =>
          match a mod 2 with
          | 0 =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | 1 =>
            match a/2 with
            | a => Some (2,2+a+c,1)
            end
          | _ => Some x
          end
        end
      | _ => Some x
      end
    | _ => Some x
    end)
    (fun x =>
    let '(a,b,c) := x in
    match N'OS b with
    | None =>
      match N'OS (c mod 2) with
      | None =>
        match c/2 with
        | c => Some (1+a,c,0)
        end
      | Some cmod2 =>
      match N'OS (cmod2) with
      | None =>
        match N'OS (c/2) with
        | None =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (2,a,2)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => None
            end
          | _ => Some x
          end
          end
        | Some c => Some (3+a,c,1)
        end
      | _ => Some x
      end
      end
    | Some b =>
    match N'OS b with
    | None =>
      match N'OS (c mod 2) with
      | None =>
        match c/2 with
        | c =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (2,1+a+c,1)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | _ => Some x
          end
          end
        end
      | Some cmod2 =>
      match N'OS (cmod2) with
      | None =>
        match c/2 with
        | c =>
          match N'OS (a mod 2) with
          | None =>
            match a/2 with
            | a => Some (0,3+a+c,0)
            end
          | Some amod2 =>
          match N'OS (amod2) with
          | None =>
            match a/2 with
            | a => Some (2,2+a+c,1)
            end
          | _ => Some x
          end
          end
        end
      | _ => Some x
      end
      end
    | _ => Some x
    end
    end)%N'
  ).
Proof.
  solve_Cert_WF.
Qed.


