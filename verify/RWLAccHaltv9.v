From BusyCoq Require Import RWLAcc62_BigUint.

Lemma tm1: halts_at_trans (TM_from_str "1RB0LD_1RC1LF_1LA1RF_0LA0RE_1LD---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0LA_0RC---_1RA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB0RE_1RC1RE_1LD0LC_0RA1LC_0LF1RA_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB0LF_0LC0RD_1LE1RD_1LE0RE_1LA0RE_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB---_1LC0RD_1RE0LD_0RE0LB_0LB0RF_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB0RA_1LC0LC_1RD0LB_1RE0LE_0RA0RF_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0RF_0RC---_1LD1RD_0LE0LD_1RA1LE_0RD1RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB---_0RC1LF_0RD1LE_1LD0LA_1RF0LE_0LC0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_0LD1RA_1LE1LB_0LA1LC_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB0LC_0RC0RE_1LD1LA_0LA0LD_1RB0RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0RB_0RC---_1RA1LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB0RF_0RC---_1LD1RD_0LE0LD_1RA1LE_0RD1LB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0LE_1LC1RE_0RE1LD_1LB0LC_0RF1RA_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0LA_1LC0RE_0RF0LD_1RA0RB_0RC---_1RA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0RE_0LC1LA_1LD1RC_1RA0LE_1RF0LB_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_1LD1RA_1LB1LD_0RC0RC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB1RB_1LC1RE_0RE1LD_1LB0LC_0RF1RA_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_1LD1RA_1LB1LD_0RC0LA_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB0LE_1RC0LC_0RD0RF_1RE0RD_1LA0LA_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_0RE0LD_0LC0LB_1RA1LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB1RE_1RC0RF_1LD1RA_1LB1LD_1LA0RC_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0LD_0LC1RA_1RD1LC_0RE1LB_0RA1RF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1LD0LB_0LE0LD_1LA1LB_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_0RD0RC_1RE1RA_1LA1RF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB1RF_1RC0LE_0RD0RA_1LE---_1LF0LC_1RA1LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LB_0RC0RF_1RD0RC_1LE0LE_1RA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0LB_1LC0LD_1RD1LC_1LF0RE_1RC1RE_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB---_1RC1RE_0RD1LD_0LD1LE_1RF0LE_0RC0RA") c0 (A,1).
Proof. solve_halt' 48 20000 false 2%N (10^12)%N. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB0RE_0RC0RB_1RD1RE_1LE1RF_1RA0LD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB1LA_1RC0RA_1LD0RF_0RA0LE_0LD0LC_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_1LD1RC_1LA0LC_0RB0RA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0RF_0LC0RE_0LD1LC_1LE0LA_1RB1RD_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB1LC_1LA0RF_0LD---_0LE1LE_0LB1RE_1RB0RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1LA0LC_0RE---_0RF1RF_0RA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0RA_1LC0RA_1RF1LD_0LE---_0LF1LF_0LB1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB1RC_1LC1RF_1RD0LB_1RE0RC_0RA0RE_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB---_1RC0LF_1RD0LD_0RE0RA_1RF0RE_1LB0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0RB_0RC---_1LD0RD_1LE0LA_1LF0LE_0LA0LB") c0 (B,1).
Proof. solve_halt. Time Qed.

