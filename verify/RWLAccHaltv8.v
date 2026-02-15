From BusyCoq Require Import RWLAcc62_BigUint.

Lemma tm1: halts_at_trans (TM_from_str "1RB1RD_1RC0RA_1LD0RB_0LE0LC_0LA0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE---_0RF1RD_1RA1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0RA_1LC1LB_1LE0LD_1LB---_1RF0LC_0RA0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB0RF_0RC0RA_1RD1LD_1LE---_1LA1LB_0LE0LD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA1LD_0LC0LA_0RF1RD_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LD1LB_1LA1LC_1RF1RB_0LD1RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB---_1LC1LF_0RD1LC_1RA1RE_0RD1RF_1RE0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1LB0LF_1LC1RE_1LD0LB_1RB1RA_0RB0RC_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LD1RB_0LE0LC_1RA1LF_0RD1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB---_0RC1RA_1RD1RB_1RE0LF_1LD0RA_1LD0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0RF1RE_1LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0RF1LE_1LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LF_1RA1RC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LF_1RA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1RD_1RA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LD_1RA0LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1RA_1RC0RF_1LD0RB_0LE0LC_1LA0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1LE0LD_1RA1RE_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB---_1RC1RB_1RD0RA_1LE0RC_0LF0LD_1LB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1LB_1LC0RC_1RE0LD_0RE0LA_1RA1RF_---1RC") c0 (F,0).
Proof. solve_halt'' 16 true. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0RD_1LC1LD_1RD0LB_1LC0RE_0RF1RA_---1RC") c0 (F,0).
Proof. solve_halt' 21 10000 false 2%N (10^10)%N. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1RD0RC_1LA0LD_1LB0LF_0RA---") c0 (F,1).
Proof. solve_halt' 19 10000 false 2%N (10^10)%N. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_1RD0LB_1LA0LD_1RC0RF_0LB---") c0 (F,1).
Proof. solve_halt' 19 10000 false 2%N (10^10)%N. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_0LE---") c0 (F,1).
Proof. solve_halt' 19 10000 false 2%N (10^10)%N. Time Qed.



