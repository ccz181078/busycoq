From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import CubicCap.
From BusyCoq Require Import CubicCup.

Ltac solve_halt :=
  time vm_compute;
  reflexivity.



Definition tm1 := Eval compute in (TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_1RD0RB").
Lemma halt1:halts tm1 c0.
Proof.
  apply (Cert_WF_halt WF1 750000000).
  solve_halt.
Time Qed.

Definition tm2 := Eval compute in (TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RE1RF_---0LC_0RC0RB").
Lemma halt2:halts tm2 c0.
Proof.
  apply (Cert_WF_halt WF2 750000000).
  solve_halt.
Time Qed.

Definition tm3 := Eval compute in (TM_from_str "1RB0LC_1LA1RB_1RD1LC_1RA1RE_0RF0RB_---1LC").
Lemma halt3:halts tm3 c0.
Proof.
  apply (Cert_WF_halt WF3 750000000).
  solve_halt.
Time Qed.

Definition tm4 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1RD0LA_1LC1RD_1RF0RD_---1RE").
Lemma halt4:halts tm4 c0.
Proof.
  apply (Cert_WF_halt WF4 750000000).
  solve_halt.
Time Qed.

Definition tm5 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD0LA_1LC1RD_1RF0RD_---1RE").
Lemma halt5:halts tm5 c0.
Proof.
  apply (Cert_WF_halt WF5 750000000).
  solve_halt.
Time Qed.

Definition tm6 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD0LA_1LC1RD_0RF0RD_---1LA").
Lemma halt6:halts tm6 c0.
Proof.
  apply (Cert_WF_halt WF6 750000000).
  solve_halt.
Time Qed.

Definition tm7 := Eval compute in (TM_from_str "1LB0RB_1LC1RB_1RC0LD_1RE1LD_1RF1RA_---0RD").
Lemma halt7:halts tm7 c0.
Proof.
  apply (Cert_WF_halt WF7 750000000).
  solve_halt.
Time Qed.

Definition tm8 := Eval compute in (TM_from_str "1RB1LA_1RC1RC_1RD0RD_1LE1RD_1RF0LA_---1RE").
Lemma halt8:halts tm8 c0.
Proof.
  apply (Cert_WF_halt WF8 750000000).
  solve_halt.
Time Qed.

Definition tm9 := Eval compute in (TM_from_str "1RB1LA_1RC1RC_1LD0RD_1LE1RD_1RF0LA_---1RE").
Lemma halt9:halts tm9 c0.
Proof.
  apply (Cert_WF_halt WF9 750000000).
  solve_halt.
Time Qed.

Definition tm10 := Eval compute in (TM_from_str "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1LA0RA_---1RD").
Lemma halt10:halts tm10 c0.
Proof.
  apply (Cert_WF_halt WF10 750000000).
  solve_halt.
Time Qed.

Definition tm11 := Eval compute in (TM_from_str "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---1RD").
Lemma halt11:halts tm11 c0.
Proof.
  apply (Cert_WF_halt WF11 750000000).
  solve_halt.
Time Qed.

Definition tm12 := Eval compute in (TM_from_str "1LB1RA_1RB0LC_1RD1LC_1RF1RE_1RA0RA_---0RC").
Lemma halt12:halts tm12 c0.
Proof.
  apply (Cert_WF_halt WF12 750000000).
  solve_halt.
Time Qed.

Definition tm13 := Eval compute in (TM_from_str "1RB0LD_1LC1RE_1LA1RC_1RB1LD_1RF0RC_---0LD").
Lemma halt13:halts tm13 c0.
Proof.
  apply (Cert_WF_halt WF13 750000000).
  solve_halt.
Time Qed.

Definition tm14 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE").
Lemma halt14:halts tm14 c0.
Proof.
  apply (Cert_WF_halt WF14 750000000).
  solve_halt.
Time Qed.

Definition tm15 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA").
Lemma halt15:halts tm15 c0.
Proof.
  apply (Cert_WF_halt WF15 750000000).
  solve_halt.
Time Qed.

Definition tm16 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RC_1RB0LA_1RF0RC_---0LA").
Lemma halt16:halts tm16 c0.
Proof.
  apply (Cert_WF_halt WF16 750000000).
  solve_halt.
Time Qed.

Definition tm17 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA").
Lemma halt17:halts tm17 c0.
Proof.
  apply (Cert_WF_halt WF17 750000000).
  solve_halt.
Time Qed.

Definition tm18 := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC").
Lemma halt18:halts tm18 c0.
Proof.
  apply (Cert_WF_halt WF18 750000000).
  solve_halt.
Time Qed.

Definition tm19 := Eval compute in (TM_from_str "1RB1LA_1RC1RD_1LA1RE_1RF0RC_1LF1RE_---0LA").
Lemma halt19:halts tm19 c0.
Proof.
  apply (Cert_WF_halt WF19 750000000).
  solve_halt.
Time Qed.

Definition tm20 := Eval compute in (TM_from_str "1RB1LA_1LC1RF_1LA1RD_1LE1RD_---0LA_1RE0RC").
Lemma halt20:halts tm20 c0.
Proof.
  apply (Cert_WF_halt WF20 750000000).
  solve_halt.
Time Qed.

Definition tm21 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD1RC_1RF0LA_1RD0RC_---1RE").
Lemma halt21:halts tm21 c0.
Proof.
  apply (Cert_WF_halt WF21 750000000).
  solve_halt.
Time Qed.

Definition tm22 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD1RC_0RF0LA_1RD0RC_---1LA").
Lemma halt22:halts tm22 c0.
Proof.
  apply (Cert_WF_halt WF22 750000000).
  solve_halt.
Time Qed.

Definition tm23 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD1RC_0RA0LA_1RF0RC_---0LA").
Lemma halt23:halts tm23 c0.
Proof.
  apply (Cert_WF_halt WF23 750000000).
  solve_halt.
Time Qed.

Definition tm24 := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD1RC_---0LA_1RD0RF_1LA1RC").
Lemma halt24:halts tm24 c0.
Proof.
  apply (Cert_WF_halt WF24 750000000).
  solve_halt.
Time Qed.

Definition tm33 := Eval compute in (TM_from_str "1RB1LA_1RC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE").
Lemma halt33:halts tm33 c0.
Proof.
  apply (Cert_WF_halt WF33 750000000).
  solve_halt.
Time Qed.

Definition tm34 := Eval compute in (TM_from_str "1RB1LA_1LC0LE_1LD1RC_1RF0LA_1RD0RC_---1RE").
Lemma halt34:halts tm34 c0.
Proof.
  apply (Cert_WF_halt WF34 750000000).
  solve_halt.
Time Qed.

Definition tm35 := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0LA_0LA---_1RC0RF_1LA0RC").
Lemma halt35:halts tm35 c0.
Proof.
  apply (Cert_WF_halt WF35 750000000).
  solve_halt.
Time Qed.




Definition tm25 := Eval compute in (TM_from_str "1LB1RD_1RC0LC_1RA1LC_1RF0RE_1LB1RE_---1RA").
Lemma halt25:halts tm25 c0.
Proof.
  apply (Cert_WF_halt WF25 4000000000).
  solve_halt.
Time Qed.


Definition tm26 := Eval compute in (TM_from_str "1RB0LB_1RC1LB_0LD1RE_1LA1RD_1RF0RD_---0RB").
Lemma halt26:halts tm26 c0.
Proof.
  apply (Cert_WF_halt WF26 4000000000).
  solve_halt.
Time Qed.


Definition tm27 := Eval compute in (TM_from_str "1RB0LB_1RC1LB_1LA1RD_1RE0RF_---0RB_1LA1RF").
Lemma halt27:halts tm27 c0.
Proof.
  apply (Cert_WF_halt WF27 4000000000).
  solve_halt.
Time Qed.


Definition tm28 := Eval compute in (TM_from_str "1LB1RA_1LC0LC_1RD1LC_1LB1RE_1RF0RA_---1RD").
Lemma halt28:halts tm28 c0.
Proof.
  apply (Cert_WF_halt WF28 4000000000).
  solve_halt.
Time Qed.


Definition tm29 := Eval compute in (TM_from_str "1LB1RA_1LC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD").
Lemma halt29:halts tm29 c0.
Proof.
  apply (Cert_WF_halt WF29 4000000000).
  solve_halt.
Time Qed.


Definition tm30 := Eval compute in (TM_from_str "1LB1RA_1RC0LC_1RD1LC_1LB1RE_0RF0RA_---0LB").
Lemma halt30:halts tm30 c0.
Proof.
  apply (Cert_WF_halt WF30 4000000000).
  solve_halt.
Time Qed.


Definition tm31 := Eval compute in (TM_from_str "1LB1RA_1RC0LC_1RD1LC_0LA1RE_1RF0RA_---1RD").
Lemma halt31:halts tm31 c0.
Proof.
  apply (Cert_WF_halt WF31 4000000000).
  solve_halt.
Time Qed.


Definition tm32 := Eval compute in (TM_from_str "1LB1RA_1RC0LC_1RD1LC_0LA1RE_0RF0RA_---0LB").
Lemma halt32:halts tm32 c0.
Proof.
  apply (Cert_WF_halt WF32 4000000000).
  solve_halt.
Time Qed.






Definition tm36 := Eval compute in (TM_from_str "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_1RE0RA").
Lemma halt36:halts tm36 c0.
Proof.
  apply (Cert_WF_halt WF36 940000000000).
  solve_halt.
Time Qed.


Definition tm37 := Eval compute in (TM_from_str "1LB1RA_1LC0LC_1RA1LD_1RE1LD_---1RF_0RD0RA").
Lemma halt37:halts tm37 c0.
Proof.
  apply (Cert_WF_halt WF37 940000000000).
  solve_halt.
Time Qed.


Definition tm38 := Eval compute in (TM_from_str "1LB1LE_1LC1RB_1RB0LD_0RA1LD_1RF0RB_---1RE").
Lemma halt38:halts tm38 c0.
Proof.
  apply (Cert_WF_halt WF38 940000000000).
  solve_halt.
Time Qed.






