From BusyCoq Require Import Individual62.
From BusyCoq Require Import LongAcc.

Module LongAcc62 := LongAcc BB62.
Import LongAcc62.


Require Import String PeanoNat NArith.
Open Scope sym.

Lemma tm1: halts_at_trans (TM_from_str "1RB1LF_0RC---_1RD0RE_1RE0RA_1LF1RC_1LD0LF") c0 (B,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0RA---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0RA_1LC0RF_1LF0LD_1LE---_1RA1LB_1LD1RB") c0 (D,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1RD0RD_1LA0LE_1LD1LF_1RA---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA1RE_1LC0LA_0RF1RA_---0LC") c0 (F,0).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_0LD0LC_1LE1RF_1RA0RB_0RD---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB---_0RC0LD_1LD1RF_0LE0RB_1RB0LB_0RD1RA") c0 (A,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(2*10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0LD_1RC---_1LD1RE_0LA1LD_1RA0RF_1RC0RC") c0 (B,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RA0RE_1RF1RD_0RC---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=10) (T:=(10^5)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB---_0RC0RA_0LD0RE_1RE0LE_0RF0LC_1LC1RB") c0 (A,1).
Proof.
  eapply decide_halt with (D:=10) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RD---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=10) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RB---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=10) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB0RA_0LB0RC_1RD0LF_1LE1RA_---0LF_1LC1LD") c0 (E,0).
Proof.
  eapply decide_halt with (D:=14) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_0RF1LC_1RC---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=14) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0LD---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=14) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_1LD0RE_0LF0LE_1LA0LC_0LE---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=22) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0RD_1LC1RA_1LD0LC_1RE0LA_0RF0RA_0RA---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=22) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB0LB_0RC0LE_1RD0RC_1LB0RE_0LA1RF_0RA---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=22) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB---_1LC0LB_1RE0RD_0RA1LB_1LB1RF_1RC0RE") c0 (A,1).
Proof.
  eapply decide_halt with (D:=14) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RD---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=20) (T:=(2*10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB0RA_1LC1RB_1LF1LD_1RE0LC_---1RD_1RA1LC") c0 (E,0).
Proof.
  eapply decide_halt with (D:=6) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1LB0LA_0LC0LE_1RD---_1RE1RD_1LF0RD_1RB1LA") c0 (C,1).
Proof.
  eapply decide_halt with (D:=8) (T:=(10^7)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD0LD_0LE---") c0 (F,1).
Proof.
  eapply decide_halt with (D:=8) (T:=(10^6)%N) (T0:=(10^5)).
  native_check_eq.
Time Qed.



