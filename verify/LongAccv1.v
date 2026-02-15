From BusyCoq Require Import Individual62.
From BusyCoq Require Import LongAcc.

Module LongAcc62 := LongAcc BB62.
Import LongAcc62.


Require Import String PeanoNat NArith.
Open Scope sym.

Lemma tm1: ~halts (TM_from_str "1LB0RA_1LC1RB_1RB1LD_1LE0LC_1RA0LF_0LE---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=300%N) (P':=10) (P:=8%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LF0LA_1LE0RD_1LC---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=200%N) (P':=O) (P:=1%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm3: ~halts (TM_from_str "1LB---_0LC0LF_1RD0LB_0RD0RE_1LA1LC_1LE1LB") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=250%N) (P':=11) (P:=20%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LF0LA_1RF1RB_1LC---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=200%N) (P':=1%nat) (P:=1%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB0LA_1LC0RE_0LC1LD_1LA0LF_0RB0RD_0RE---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=900%N) (P':=O) (P:=1%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0LF_1LB0RE_0LD---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=900%N) (P':=9) (P:=8%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm7: ~halts (TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_1LA---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=800%N) (P':=50) (P:=43%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm8: ~halts (TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_0RB---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=800%N) (P':=50) (P:=43%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB1RE_0RC---_1LD0LA_1RA0LA_0RF0RA_1LF0LC") c0.
Proof.
  eapply decide_loop' with (D:=40) (PP:=600%N) (P':=9) (P:=2%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0LA_0RC1RB_1RD0LC_0LE0RB_---1LF_0LA1LE") c0.
Proof.
  eapply decide_loop' with (D:=40) (PP:=1863%N) (P':=300) (P:=63%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm11: ~halts (TM_from_str "1LB1LC_1LC---_1RD1LF_1RE0RD_1LF0LC_1LA0LD") c0.
Proof.
  eapply decide_loop' with (D:=100) (PP:=300%N) (P':=1%nat) (P:=1%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB---_1LC0LE_0LA1LD_1RE1LB_1RF0RE_1LB0LD") c0.
Proof.
  eapply decide_loop' with (D:=100) (PP:=300%N) (P':=1%nat) (P:=1%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.


Lemma tm13: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE1LF_1LB0RE_0LB---") c0.
Proof.
  eapply decide_loop' with (D:=10) (PP:=4000%N) (P':=5) (P:=2%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm14: ~halts (TM_from_str "1LB0LD_1RC1LF_0RD0RC_1LE0LB_0LB---_1LA1RF") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=1000%N) (P':=296) (P:=704%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.


Lemma tm15: ~halts (TM_from_str "1LB0LE_1RC0LA_1LB1RD_0RB0RF_1LA1LA_0RD---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=16000%N) (P':=1000) (P:=931%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0LC_1LA0RE_1RD0LD_1RB1LC_1RA0RF_0RE---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=16000%N) (P':=1000) (P:=931%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0LA_1LC0RE_0LC1LD_1LA0LF_0RB0RD_1LE---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=1000%N) (P':=500) (P:=435%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB1LD_1RC0RE_1LA1RC_0LC0LA_0RF0RD_---0RB") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=1000%N) (P':=100) (P:=201%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm19: ~halts (TM_from_str "1LB0LE_1RC1LD_1RA0RC_1LA0LB_1LF1RC_0LD---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=6000%N) (P':=3000) (P:=2908%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm20: ~halts (TM_from_str "1LB1RE_1LC0RE_1LD0LC_0RA1RD_1RF0RB_1RC---") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=1000%N) (P':=800) (P:=2%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm21: ~halts (TM_from_str "1LB0LD_1RC1LF_0RD0RC_1LE0LB_1LF---_1LA0LB") c0.
Proof.
  eapply decide_loop' with (D:=20) (PP:=800%N) (P':=400) (P:=283%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm22: ~halts (TM_from_str "1LB1RA_1LC0LE_1RD1LA_0RE0RD_1LF0LC_0LC---") c0.
Proof.
  eapply decide_loop' with (D:=60) (PP:=1000%N) (P':=400) (P:=704%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1LD_1RC0RE_1LA1RC_0LC0LA_0RF1RA_---0RB") c0.
Proof.
  eapply decide_loop' with (D:=6) (PP:=1500%N) (P':=400) (P:=156%N) (T0:=(10^5)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB1LF_0RC0RB_0LD0LA_1RE---_1LA0LC_1LE0LA") c0.
Proof.
  eapply decide_loop' with (D:=60) (PP:=6000%N) (P':=2000) (P:=832%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB1LD_1RC0RE_1LA1RC_0LC0LA_0RF1RE_---0RB") c0.
Proof.
  eapply decide_loop' with (D:=6) (PP:=2200%N) (P':=500) (P:=6453%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB1LB_1LC1LA_1RD0LB_1LF1RE_0RC0RE_---0LD") c0.
Proof.
  eapply decide_loop' with (D:=10) (PP:=3500%N) (P':=3000) (P:=3887%N) (T0:=(10^6)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

Lemma tm27: ~halts (TM_from_str "1LB0LC_1RC0LC_1RF1RD_0RE0RC_1LE0LA_0RA---") c0.
Proof.
  eapply decide_loop' with (D:=40) (PP:=7000%N) (P':=20) (P:=2%N) (T0:=(10^7)%N) (T1:=(10^5)).
  intros.
  native_check_eq.
Time Qed.

