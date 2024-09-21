From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import CubicCap.

Ltac solve_halt :=
  time vm_compute;
  reflexivity.



Definition tm23 := Eval compute in (TM_from_str "1LB0LC_1RC1LA_0RD1RC_1RE1RA_1LF1RC_---0LE").
Lemma halt23:halts tm23 c0.
Proof.
  apply (Cert_WF_halt WF23 761188).
  solve_halt.
Time Qed.

Definition tm24 := Eval compute in (TM_from_str "1LB0LD_1RC1LA_1LF1RD_0RE1RD_1RC1RA_---0LC").
Lemma halt24:halts tm24 c0.
Proof.
  apply (Cert_WF_halt WF24 761188).
  solve_halt.
Time Qed.

Definition tm25 := Eval compute in (TM_from_str "1LB0LC_1RB1LA_0RD1RC_1RE1RA_1LF1RC_---0LE").
Lemma halt25:halts tm25 c0.
Proof.
  apply (Cert_WF_halt WF25 761188).
  solve_halt.
Time Qed.

Definition tm26 := Eval compute in (TM_from_str "1LB0LC_0LC1LA_0RD1RC_1RE1RA_1LF1RC_---0LE").
Lemma halt26:halts tm26 c0.
Proof.
  apply (Cert_WF_halt WF26 761188).
  solve_halt.
Time Qed.

Definition tm42 := Eval compute in (TM_from_str "1RB1LF_1LC0RA_0RD1LB_---1RE_1RD1RB_0LA0LB").
Lemma halt42:halts tm42 c0.
Proof.
  apply (Cert_WF_halt WF42 880039).
  solve_halt.
Time Qed.

Definition tm37 := Eval compute in (TM_from_str "1RB0LE_1LC1RA_1RA1LD_0LC0LA_1RE1RF_0RC---").
Lemma halt37:halts tm37 c0.
Proof.
  apply (Cert_WF_halt WF37 14357308).
  solve_halt.
Time Qed.

Definition tm38 := Eval compute in (TM_from_str "1RB1LD_1RC0LE_1LA1RB_0LA0LB_1RE1RF_0RA---").
Lemma halt38:halts tm38 c0.
Proof.
  apply (Cert_WF_halt WF38 14356678).
  solve_halt.
Time Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB1RE_0LC1RA_---1LD_0LE1RD_0RA1LF_1LC0LA").
Lemma halt3:halts tm3 c0.
Proof.
  apply (Cert_WF_halt WF3 140691045).
  solve_halt.
Time Qed. (* 60s *)

Definition tm28 := Eval compute in (TM_from_str "1RB0LB_1LC0LF_0LE1RD_1LE0RC_1LA1LD_---1RA").
Lemma halt28:halts tm28 c0.
Proof.
  apply (Cert_WF_halt WF28 151147258).
  solve_halt.
Time Qed.

Definition tm45 := Eval compute in (TM_from_str "1RB0LB_1LC1RA_---0LD_1LA1LE_1LD0RF_1RD1RE").
Lemma halt45:halts tm45 c0.
Proof.
  apply (Cert_WF_halt WF45 439817653).
  solve_halt.
Time Qed.

Definition tm41 := Eval compute in (TM_from_str "1LB1LE_0LC0LD_1RD1LB_1RE0RC_1LF1RD_---1LA").
Lemma halt41:halts tm41 c0.
Proof.
  apply (Cert_WF_halt WF41 1236859225).
  solve_halt.
Time Qed.

Definition tm13 := Eval compute in (TM_from_str "1RB1LD_0LC1RA_1LA1LB_1LE1RE_---0RF_1RC1LB").
Lemma halt13:halts tm13 c0.
Proof.
  apply (Cert_WF_halt WF13 3616249401).
  solve_halt.
Time Qed.

Definition tm14 := Eval compute in (TM_from_str "1LB1LC_1RC1LD_0LA1RB_1LE1RE_---0RF_1RA1LC").
Lemma halt14:halts tm14 c0.
Proof.
  apply (Cert_WF_halt WF14 3616249399).
  solve_halt.
Time Qed.

Definition tm46 := Eval compute in (TM_from_str "1LB1RC_0RC1LD_1RA1RB_1LE0LF_---0LA_1LC1RB").
Lemma halt46:halts tm46 c0.
Proof.
  apply (Cert_WF_halt WF46 9477135359).
  solve_halt.
Time Qed.

Definition tm27 := Eval compute in (TM_from_str "1LB1RD_1RC1RD_1LD1RB_0RB1LE_1LF0LA_---0LC").
Lemma halt27:halts tm27 c0.
Proof.
  apply (Cert_WF_halt WF27 9477135357).
  solve_halt.
Time Qed.

Definition tm39 := Eval compute in (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RA_---1RA").
Lemma halt39:halts tm39 c0.
Proof.
  apply (Cert_WF_halt WF39 45934447152).
  solve_halt.
Time Qed.

Definition tm40 := Eval compute in (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RA_---1LB").
Lemma halt40:halts tm40 c0.
Proof.
  apply (Cert_WF_halt WF40 45934447152).
  solve_halt.
Time Qed.



