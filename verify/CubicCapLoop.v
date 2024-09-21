From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import CubicCap.

Ltac ind n H :=
  induction n as [|n IHn]; intros;
  [ finish |
    cbn[Nat.add];
    follow H;
    follow IHn;
    finish ].

Import UintArith.N'.

Lemma Cert_WF_steps' {tm S0 x_init bouncer_rule bouncer_rule' calc_step calc_step'}:
  Cert_WF tm (cert1 S0 x_init bouncer_rule bouncer_rule' calc_step calc_step') ->
  forall (T:N),
  option (N'*N'*N').
Proof.
  intros H T.
  apply (calc_steps' bouncer_rule' calc_step' T (N'of_nat3 x_init)).
Defined.

Definition N'to_N3(x:N'*N'*N') :=
let '(a,b,c):=x in
(N'toN a,N'toN b,N'toN c).

Definition N'to_oN3(x:option (N'*N'*N')) :=
match x with
| Some x0 => Some (N'to_N3 x0)
| None => None
end.

Definition N_to_nat3(x:N*N*N):=
let '(a,b,c):=x in
(N.to_nat a,N.to_nat b,N.to_nat c).

Lemma N'to_N3_to_nat3 x:
  N'to_nat3 x = N_to_nat3 (N'to_N3 x).
Proof.
  destruct x as [[a b] c].
  cbn.
  repeat rewrite N'toN_spec.
  reflexivity.
Qed.

Lemma Cert_WF_init' {tm S0 x_init bouncer_rule bouncer_rule' calc_step calc_step'}:
  Cert_WF tm (cert1 S0 x_init bouncer_rule bouncer_rule' calc_step calc_step') ->
  forall (T:N) x',
  N'to_oN3 (calc_steps' bouncer_rule' calc_step' T (N'of_nat3 x_init)) = Some x' ->
  c0 -[TM_from_str tm]->* config S0 (N_to_nat3 x').
Proof.
  intros H T x H0.
  unfold Cert_WF in H.
  specialize (H T).
  destruct (calc_steps' bouncer_rule' calc_step' T (N'of_nat3 x_init)).
  2: cbn in H0; congruence.
  follow H.
  finish.
  f_equal.
  cbn in H0.
  inverts H0.
  rewrite N'to_N3_to_nat3.
  reflexivity.
Qed.

Ltac rec_eq' a b :=
lia ||
match a with
| ?f ?x =>
match b with
| ?g ?y =>
replace f with g by (rec_eq' f g);
replace x with y by (rec_eq' x y);
reflexivity
end
end ||
reflexivity.

Ltac rec_eq :=
match goal with
| |- ?a = ?b => rec_eq' a b
end.

Module CubicCapLoop.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_---1LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{B}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (2+n) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs 0 0 (2+n) (2+n)).
  mid10 (S0 (5+n*2) 1 n).
  1: solve_rule.
  follow (Incs (5+n) 1 0 n).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF1 301 (151,0,302)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 149).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1LE_1RD1LB_---1RC_1RA1RF_0LB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF2 10002 (17367%N, 0%N, 6944%N)).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM2.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1LE_1RD1LB_---1RC_0LB1RF_0RA0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF4 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1LE_1RD1LB_---1RC_0RA1RF_0LB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF5 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC1LD_1RD1LB_0LB1RE_1RF0RA_---1RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^(a) <{{D}} [1;0]^^(b) *> [1]^^(1+c) *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (2+n*2) 0 (12+n*8).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs 0 0 (10+n*6) (2+n*2)).
  mid10 (S0 (7+n*4) 0 (10+n*6)).
  1: solve_rule.
  follow (Incs 0 0 (3+n*2) (7+n*4)).
  mid (S0 (17+n*8) 1 (1+n*2)).
  1: solve_rule.
  follow (Incs (16+n*6) 1 0 (1+n*2)).
  mid (S0 (14+n*6) 0 (8+n*4)).
  1: solve_rule.
  follow (Incs (6+n*2) 0 0 (8+n*4)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF6 1000001 (500020%N, 0%N, 2000084%N)).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 250009).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM6.



Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1LE_1RD1LB_---1RC_0LB1RF_---0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF7 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM7.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1LE_1RD1LB_---0LE_0LB1RF_1RC0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF8 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.
End TM8.



Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1LE_1RD1LB_---1RC_0LB1RA_1RB1LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF9 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.
End TM9.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1LE_1RD1LB_---1RC_0LB1RF_0LB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF10 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM10.



Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC1LE_1RD1LB_---1RC_0LB1RF_0RB0RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{E}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF11 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1LB1LC_0RC0RA_0LD1RB_1LE1LC_1RF1LD_---1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^a <{{C}} [1] *> [0;1]^^b *> [1]^^c *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF12 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM12.



Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1LC0RA_1RE1LD_1LC1LF_---1RC_0LD1RB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^(a) <{{F}} [1] *> [0;1]^^(b) *> [1]^^(c) *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF18 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM18.


Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0RC0RA_0LD1RB_1LE1LC_1RF1LD_---1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^(a) <{{C}} [1] *> [0;1]^^(b) *> [1]^^(c) *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (17+n*5) 0 (4+n*2).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (13+n*3) 0 0 (4+n*2)).
  mid10 (S0 (11+n*3) 0 (12+n*4)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (11+n*3)).
  mid (S0 (25+n*6) 0 (1+n)).
  1: solve_rule.
  follow (Incs (24+n*5) 0 0 (1+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF19 10002 (17367,0,6944)%N).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 3470).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM19.


Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC1LA_1RD1RA_1LF1RE_0LB1RE_---0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym.

Lemma Inc a b c:
  S0 (2+a) b (1+c) -->* S0 (a) (2+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n*2+a) b (n+c) -->* S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (7+n*4) 0 (n).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (7+n*2) 0 0 n).
  mid10 (S0 (4+n*2) 0 (3+n*2)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (2+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF43 1001 (1935%N, 0%N, 482%N)).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 482).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM43.


Module TM44.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1LC1LA_1RD1RA_1LF1LE_0LB1RE_---0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1]^^(a) <{{A}} [1;1]^^(b) *> [1;0]^^(c) *> const 0)%sym.

Lemma Inc a b c:
  S0 (2+a) b (1+c) -->* S0 (a) (2+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n*2+a) b (n+c) -->* S0 a (n*2+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Definition config n:=
  S0 (7+n*4) 0 (n).

Lemma config_S n:
  config n -->+ config (S n).
Proof.
  unfold config.
  follow (Incs (7+n*2) 0 0 n).
  mid10 (S0 (4+n*2) 0 (3+n*2)).
  1: solve_rule.
  follow (Incs 0 0 (1+n) (2+n)).
  solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF44 1001 (1935%N, 0%N, 482%N)).
    vm_compute.
    reflexivity.
  }
  exists (N.to_nat 482).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  intros i.
  eexists.
  apply config_S.
Qed.

End TM44.

Module TM30.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC0LA_1RD0RE_1LE1RD_1LA1LF_1RF0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S0 :=
  (fun a b c => const 0 <* [1;0]^^(a) <{{F}} [1;1] *> [1;1;1;1]^^(b) *> [1;0]^^(c) *> [1;1;1;1] *> const 0)%sym.

Lemma Inc a b c:
  S0 (1+a) b (1+c) -->* S0 (a) (1+b) (c).
Proof.
  solve_rule.
Qed.

Lemma Incs a b c n:
  S0 (n+a) b (n+c) -->* S0 a (n+b) c.
Proof.
  gen a b c.
  ind n Inc.
Qed.

Inductive Config :=
| C601(n:nat)
| C502(n:nat)
| C304(n:nat)
.

Definition config(x:Config):=
match x with
| C601 n => S0 (3+n*6) 0 (1+n)
| C502 n => S0 (4+n*5) 0 (3+n*2)
| C304 n => S0 (n*3) 0 (3+n*4)
end.

Lemma config_S:
  forall x:Config, exists y:Config, config x -->+ config y.
Proof.
  intros x.
  destruct x as [n|n|n]; unfold config.
  - destruct (Nat.Even_or_Odd n) as [[n0 H]|[n0 H]]; subst n.
    + exists (C502 (n0*2)).
      follow (Incs (2+n0*10) 0 0 (1+n0*2)).
      solve_rule.
    + exists (C502 (1+n0*2)).
      follow (Incs (7+n0*10) 0 0 (2+n0*2)).
      mid10 (S0 0 (3+n0*5) (7+n0*4)); solve_rule.
  - destruct (Nat.Even_or_Odd n) as [[n0 H]|[n0 H]]; subst n.
    + exists (C304 (1+n0*2)).
      follow (Incs (1+n0*6) 0 0 (3+n0*4)).
      mid10 (S0 0 (n0*3) (9+n0*8)); solve_rule.
    + exists (C304 (2+n0*2)).
      follow (Incs (4+n0*6) 0 0 (5+n0*4)).
      solve_rule.
  - exists (C601 n).
    follow (Incs 0 0 (3+n) (n*3)).
    solve_rule.
Qed.

Lemma init:
  exists n, c0 -->* config n.
Proof.
  eassert _ as H. {
    apply (Cert_WF_init' WF30 10001 (14811%N, 0%N, 2469%N)).
    vm_compute.
    reflexivity.
  }
  exists (C601 (N.to_nat 2468)).
  follow H.
  unfold config,S0,CubicCap.config,N_to_nat3.
  apply evstep_refl'.
  rec_eq.
Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  destruct init as [n0 Hinit].
  eapply multistep_nonhalt.
  1: apply Hinit.
  apply progress_nonhalt_simple.
  apply config_S.
Qed.

End TM30.

End CubicCapLoop.


