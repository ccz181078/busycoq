From BusyCoq Require Import RWLAcc62_BigUint.


Lemma tm1: halts_at_trans (TM_from_str "1RB0LB_0RC1RC_1RD---_1RE1LD_1LF0RA_0LD0LF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB1RD_0RC1RC_1RD---_1RE1LD_1LF0RA_0LD0LF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0LB_0RC0RD_0LD1RC_1LE0RA_1LA0LF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB0RF_1LC0RC_0LE0LD_1RA0LB_0RD1LE_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB0LB_0RC0RD_0LD1RC_1LE0RA_1LA1LF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0LB_0RC0RD_0LD1RC_1LE0RA_1LA1LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1RF_1LC0RC_0LE0LD_1RA0LB_0RD1LE_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB1RF_1LC0RC_0LE0LD_1RA0LB_0RD1LE_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB0LB_0RC0RD_0LD1RC_1LE0RA_0RE1LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB---_1LC0RC_0LF0LD_1RE0LB_0LE1RA_0RD1LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB---_1LC0RC_0LF0LD_1RE0LB_1RB1RA_0RD1LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB0LD_0RC0RA_1LC1LA_0LE0LF_1LA0RD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RD0LB_1LB1RE_1LC0RE_0LD1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0LC_1LC1RF_1LA0RD_0LB1RE_1RC---_1LA0RF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1RA1LD_1RB0LD_0RC1LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LA_1LC0RD_1RD1LA_1RB0LE_0RC1LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB0LF_0RC1RB_0RD0LE_1LD0RE_1LA1LE_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB1RD_1RC1RF_0LD0LC_1RE1LD_1LC0RA_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB1RC_1LC1RF_1RD1LC_1LE0RA_0LC0LE_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RC_1LA1RF_1RD1LC_1LE0RA_0LC0LE_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0RA1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0LF1RA_1LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0RD_1RC1LF_1RD---_1RE1RF_1LB0LF_1RA0LB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB1LE_1RC---_1RD1RE_1LA0LE_1RF0LA_1RA0RC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB---_1RC1RE_1LD0LE_1RA1LE_1RF0LD_1RD0RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0LB_0RC0RD_1LA0LE_1RE0RA_1LC0RF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LD_1RC0RF_1LA0RA_1LE0LE_1RC0LA_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0RB_1LC0RF_1LD1RC_1RA1LE_0LD0LA_---0RC") c0 (F,0).
Proof. solve_halt'' 15 true. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1LD0LD_1RA0LF_0RB0RC_---0LA") c0 (F,0).
Proof. solve_halt'' 15 true. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB0LC_0LA1RD_1LA0LF_0RE---_1RC1RE_0LE0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0RB1LD_0LE---_1LA1LE_0RE0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_1RD0LB_0LC1RE_0RA---_0LA0RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0RF_1RC0LC_1RD0LA_1LE0RC_1LB0LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0LF_0RC0RA_1LD0LA_0LD0RE_1LF---_1LA0LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD0LA_1LD1LA_1LA0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0LE_0LC0RF_1LD1LC_0RA0LE_1RD0LC_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_0LB0LE_1RA0RB_1LF1LC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LE0RD_0RD1LB_1RA0LF_1RA0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LE0RD_0RD1LB_1RA0LF_0RC0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB---_1LC0RE_0LE0RD_1LF1LB_1RA0LF_0RC0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_0RA0LD_1LC1LF_1RA0LB_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB1LC_0RC0RA_0LD1RE_1LB1LF_1RC0RA_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0RA_0RC1LD_1RD1LE_0LB1RC_1RF0LF_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB0RA_0RC1LE_1RD1RB_0LB1RC_0LB0LF_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB0LF_1RC1LD_1LD1RE_0LA1LE_0RB1RA_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1RD0RF_1LE1RE_1LA0LD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_0RD0RF_1LE1RE_1LA0LD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB0RA_0RC1RF_1LD1RC_1LE1LF_0RC1LD_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB---_0RC0RE_1LD1RC_0LE1LB_1RB0LF_1LE0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD1RC_0LA1LB_1LA0LF_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD1RC_0LA1LB_1LA0LF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LE_1LC1RA_0LD0LC_1RD0RA_1LC0LF_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB1LC_1RC1RF_1LA1RD_0RE1LE_1RC0LA_---0RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB0RD_0RC0LD_1LC0RB_0LE1RF_1RA1LE_---0RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB0RF_0RC---_1RD0LF_1LE0LF_1RA1LC_1RE0LE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB1RF_1RC0RD_0LB0RE_1RE---_1LF0LE_1RA1LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB1LD_1RC1RA_1RD0RE_0LC0RF_1RF---_1LA0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB---_1LC0LB_1RF1LD_0LE0RB_1RD0RA_1RE1RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB0RA_1LC1RE_1LD1LB_1LE0LF_0RD0LA_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0RC_0LA0RD_1RD---_1LE0LD_1RF1LB_1RA1RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE0RB_0RE0LF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE0RB_1RE1RB_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB1LE_0RC0RF_1LD0RA_0LA0LC_0LF---_1RC0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB1LB_1RC0RA_1LD0RB_1LE0LC_0LA0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LB_1RC0RA_1LD0RB_1LE0LC_1LA0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LD0LB_0LE0LF_1RA1LA_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1LE0LF_1RA1LA_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB1RD_1LC1RA_---0LD_1LE1RB_1RF1LF_0LC0RD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA1LB_0RE0LB_1LE1LF_0LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_---1LD_1RA1LF_1RA0RE_0LE0LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB0RE_0LC1LB_1LE1LD_0LE0LF_1RA0RA_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB1RE_1LC0LC_1LD0LB_0RA1RD_0RB0RF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_0LE0LC_1RF1LE_0RC1RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD1RC_0LA1LB_1LA0LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB0RB_1RC0RE_1LD1LC_1LF1LE_1RA0LE_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB1RC_1LC1RA_1RF0RD_1LA1LE_1LD0LD_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB1RE_1LC1LD_1RD1LB_1LF0LA_1RA0RA_---1LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB0LD_0LC0RE_---1LD_1LA0LB_1RF0RD_1RD1RE") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB0LE_0RC1RB_0RD1RE_1LE---_1LF0RE_1LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB---_1RC0RF_1LD0RA_0LF0LE_1LB0LC_0RA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB---_1RC0RF_1LD0RD_0LF0LE_1LB0LC_0RA0LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB0LB_0LC1RD_1RE1LA_0RB---_1LF0RC_0LA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB1LA_1RC1RB_1LD1RF_---0LE_1LB1LE_1RD0LA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB1LF_0LB0RC_1LD0RE_1LA---_1LA1RA_1LB0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB0LE_1RC---_1LD1RF_0RD0LA_1RC1LC_1RD0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0LD_1RC0LA_1LB1RA_1LE1LA_1RF---_1RB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB0LD_1RC0LA_1LB1RA_1LE1LA_1RF---_0LC1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB1RF_1RC0LD_1LB1RD_1RB0LE_1LF1LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB---_0LC1RA_1LE1RD_1RE0LF_1RC0LD_1LA1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB---_1RC1RA_1RD0LE_1LC1RE_1RC0LF_1LA1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB1RC_0RC---_1LD1RE_1RA0LA_0RD0LF_0LD1LE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB1LE_1LC0RC_1LD1LA_0LA---_0LB0RF_0RB1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB0LB_1RC1RD_0RD---_1LA1RE_0RA0LF_0LA1LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB---_1LC0RF_0LD0LC_1RD0RE_1LC0LF_1RA0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB---_0LC1RF_1RD0LD_0RE1LD_1RA1LB_1RC0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB1LC_1RC---_0LD1RF_1RE0LE_0RA1LE_1RD0LF") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB0LB_0RC1LB_1RD1LE_1RE---_0LA1RF_1RA0LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_1RD1LE_0LA---_1LA0LC_1RA0RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB0RC_1RC0LD_1LB1RA_0LC0LE_1LF1LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB0RD_0RC1LD_1LB1RC_1LE0RF_1LB0LA_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1LC_1RC1RB_1RD0RF_0LE1LD_1LA0LD_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB1LC_1RC0LF_1RD0RF_0LE1LD_1LA0LD_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_0LE0RE_1RC1LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB1RF_1LC---_0LD1LB_1RE0LF_0RF0RF_1LE0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB0LC_0RC0RC_1LB0RD_1RE1RC_1LF---_0LA1LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm106: halts_at_trans (TM_from_str "1RB---_0RC1RA_1LD0RE_0LE0LE_1RD0LF_1LA1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm107: halts_at_trans (TM_from_str "1RB0LC_0LA0LA_1LD1LA_1RE---_0RF1RD_1LB0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm108: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_0LD0RA_1LF1LC_0RD---_1LA0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm109: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LB_1LE0LA_1RA0LF_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm110: halts_at_trans (TM_from_str "1RB1RE_1RC0RD_1LD0RF_1LE0LD_0RA0LC_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm111: halts_at_trans (TM_from_str "1RB1RF_0LC0RE_1LE1RD_1RC---_1LF0LE_0RA0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm112: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LB_0RE0LA_1RA1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm113: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LB_1LE0LA_1RA1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm114: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_0LD0RA_1LF1LC_1LA---_0RA0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm115: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_0LD0RA_1LF1LC_1LA---_1LA0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm116: halts_at_trans (TM_from_str "1RB1LE_1RC0RB_0LD0RA_1LF1LC_1LA---_1RD0LB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm117: halts_at_trans (TM_from_str "1RB1RC_1LA0RF_0RA0LD_1LF1RE_1RD---_1LC0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm118: halts_at_trans (TM_from_str "1RB1RE_1RC0RD_1LD1RF_1LE0LD_0RA0LC_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm119: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LB_1RC0LA_1RA1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm120: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1RE0LF_1RA---_1RF0LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm121: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0RE1LF_1RA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm122: halts_at_trans (TM_from_str "1RB0RC_0RC1LE_1LD1RF_1LB0LC_0LB---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm123: halts_at_trans (TM_from_str "1RB1LE_0RC0RB_1LC0LD_1LA0RA_1LF0RE_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm124: halts_at_trans (TM_from_str "1RB0RB_1LC1RB_1LE0RD_1RA1RC_---1LF_0LD0LC") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm125: halts_at_trans (TM_from_str "1RB1LF_1RC0LD_1RD0RE_1LB0LE_0LA0RB_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm126: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_0LE0LC_1RF0RC_0RF0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm127: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_0LE0LC_1RF0RC_1RF1RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm128: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1LA1LC_1RA0LE_0LF1LA_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm129: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1LA1LC_1RA0LE_1LF1LA_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm130: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1LA1LC_1RA0LE_1LF1LA_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm131: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD0RC_1RE0RF_1LA0RD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm132: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD0RC_1RE1RF_1LA0RD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm133: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE1LD_0RB0RC_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm134: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE1LD_0RB0RC_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm135: halts_at_trans (TM_from_str "1RB0RE_1LC0RC_0LA0LD_1LE0LB_1RA0LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm136: halts_at_trans (TM_from_str "1RB1LD_1RC0RA_0LA1RF_0LE0LB_1LC0LA_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm137: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RD_0LB0LE_1LA0LC_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm138: halts_at_trans (TM_from_str "1RB0RD_1LC0RF_1LD0LB_1RE0LE_0RC0RA_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm139: halts_at_trans (TM_from_str "1RB0RF_1RC0RD_1LB0RE_---1LC_1RA0LF_1LE0LE") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm140: halts_at_trans (TM_from_str "1RB0RF_1RC---_1LD0RE_1RC1LD_1RA0LF_1LE0LE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm141: halts_at_trans (TM_from_str "1RB0RE_0LC0RA_1LA1LD_1LC1LF_0LC0LD_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm142: halts_at_trans (TM_from_str "1RB0LF_1RC0LE_0LD0RA_1LA1LD_---1LB_1LD0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm143: halts_at_trans (TM_from_str "1RB0LD_1RC0LF_1LC0RA_1LE0RD_1LA1LE_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm144: halts_at_trans (TM_from_str "1RB0LE_1RC0RB_1LD0RD_0LA1RA_---1LF_1RD1LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm145: halts_at_trans (TM_from_str "1RB0LD_1RC0RB_0LD0RF_---1LE_1RF1LF_0LA1RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm146: halts_at_trans (TM_from_str "1RB0RD_0LC1LF_1LE1LD_1LB0RA_1RF1LD_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm147: halts_at_trans (TM_from_str "1RB0RD_0LC1LE_1RE1LD_1LB0RA_0LF1RA_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm148: halts_at_trans (TM_from_str "1RB1LB_1RC0RA_1LD0RB_1LE0LC_0RE0LF_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm149: halts_at_trans (TM_from_str "1RB0RF_0LB0RC_0RD---_1LE1RE_1LF0LD_1RA0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm150: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LD1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm151: halts_at_trans (TM_from_str "1RB1RD_1RC0RA_1LD0RB_0LE0LC_0RF0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm152: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0RF0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm153: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0LA0RA_1LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm154: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_0LA0RA_1LB1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm155: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_1LE0LF_1RA0LE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm156: halts_at_trans (TM_from_str "1RB0RF_1LC0RB_1LD0LB_1RE0LC_0RA0RD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm157: halts_at_trans (TM_from_str "1RB0LE_1RC0RF_1RD0RA_1LE0RC_1LC0LD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm158: halts_at_trans (TM_from_str "1RB0LF_0LB1RC_1RD---_1RE0RA_1LF0RD_1LD0LE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm159: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1RD0RA_1LE0RC_1LC0LD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm160: halts_at_trans (TM_from_str "1RB0RF_0RC0RE_0LD---_0LE1LA_1RA1LE_0LC1LD") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm161: halts_at_trans (TM_from_str "1RB0LD_0RC1RA_1RD0RF_1LA0LE_---0LF_0RA1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm162: halts_at_trans (TM_from_str "1RB0RC_1RC0LD_1LB1RA_0LC0LE_1LF1LD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm163: halts_at_trans (TM_from_str "1RB1RE_0LC0RC_0RA1LD_0LE---_0RF0LF_1LB1RC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm164: halts_at_trans (TM_from_str "1RB0LF_1LC0LE_0RD1LB_0RA1RD_---1LC_1LA1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm165: halts_at_trans (TM_from_str "1RB0LF_1LC0LE_0RD1LB_0RA1RD_---1LC_1LA1LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm166: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0LD1RF_1LE0RF_1LA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm167: halts_at_trans (TM_from_str "1RB1LC_0LC1RA_0LA0LD_1LA0RE_1RF---_0RB0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm168: halts_at_trans (TM_from_str "1RB0LE_1LC1RD_0RD1LB_0RB0RA_1LF---_0LC0LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm169: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1RD0LB_1RE1RC_1LA1LF_---1LA") c0 (F,0).
Proof. solve_halt'' 42 true. Time Qed.

Lemma tm170: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD1LB_1RE1RF_1LA0RD_---1RE") c0 (F,0).
Proof. solve_halt'' 42 true. Time Qed.

Lemma tm171: halts_at_trans (TM_from_str "1RB1RB_1LC0RA_1LE0RD_0RC1RC_1RB1LF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm172: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_1LA0RD_0RC1RC_0LB---_1RB1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm173: halts_at_trans (TM_from_str "1RB1LD_1LC0RE_1RD0LB_1LA0RC_1RB1RF_---1RB") c0 (F,0).
Proof. solve_halt'' 42 true. Time Qed.

Lemma tm174: halts_at_trans (TM_from_str "1RB1RF_1LC0RA_1RD0LB_1LE0RC_1RB1LD_---1RB") c0 (F,0).
Proof. solve_halt'' 42 true. Time Qed.

Lemma tm175: halts_at_trans (TM_from_str "1RB1LF_1RC0RD_1LD0RF_0RA0LE_1LB0LC_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm176: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1LA1LC_1RA0LE_1LF1LA_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm177: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1LD---_1LE1RA_1RD1LA_0RD1LC") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm178: halts_at_trans (TM_from_str "1RB---_1RC1LD_1LB1RD_1LE0RC_0LA0LF_0LB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm179: halts_at_trans (TM_from_str "1RB1RA_1LC1RE_1LD1LB_0RB0LF_0RA0RB_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm180: halts_at_trans (TM_from_str "1RB0RE_1LC1RE_1LD1LB_1RE0LA_0RA0LF_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm181: halts_at_trans (TM_from_str "1RB1RF_1LC0LC_1RC1LD_1RE1LF_---0RD_1RA1LB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm182: halts_at_trans (TM_from_str "1RB0LF_1LC1RD_---1LD_0RE0LA_1RF1LE_1RB0LB") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm183: halts_at_trans (TM_from_str "1RB0LB_1LC1RD_---1LD_0RE0LF_1RA1LE_1RB0LA") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm184: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_1LE0LC_1RC1LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm185: halts_at_trans (TM_from_str "1RB0RC_1LC1RE_1RA0LD_1LC0LE_1LD0RF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm186: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_1RE0RC_1LC1RF_1LB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm187: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LE0LF_1RA0RD_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm188: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0LD0LB_1LE0LF_1RA0RD_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm189: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_1LD0RC_0LA0LE_0RC0RA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm190: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LE1LD_0LB---_0RA1LE_0RA1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm191: halts_at_trans (TM_from_str "1RB0RF_1LC1RD_1LA0LB_0LC1RE_0RB0RA_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm192: halts_at_trans (TM_from_str "1RB0RF_1LC1RD_1LA0LB_0LC1RE_0RB0RA_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm193: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_1RD0LD_1LA0RF_1RF---_0RC0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm194: halts_at_trans (TM_from_str "1RB0LC_1LC0RF_0LE0LD_1LC---_1LA0RA_1RE0LB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm195: halts_at_trans (TM_from_str "1RB0LC_1LC0RF_0LE0LD_1LC---_1LA0RA_1RE0LD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm196: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_1RF0LD_1LE---_0LF0LD_1LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm197: halts_at_trans (TM_from_str "1RB0LC_1LC0RE_0LF1LD_0RE---_1RF0LB_1LA0RA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm198: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LE1LD_0LB---_0RA0LB_0RA1RF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm199: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE1LD_0RB1RC_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm200: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_0LD0LB_1RE1LD_0RB1RC_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm201: halts_at_trans (TM_from_str "1RB0RC_0LC1RF_1RA1LD_0LE0LA_1LB0LC_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm202: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_0LB0LE_1RA0RB_1LF1LC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm203: halts_at_trans (TM_from_str "1RB1LC_1LA0RD_1LB0LA_1LB0RE_0RF1RD_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm204: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1RA0LE_1RA0RB_0LF1LC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm205: halts_at_trans (TM_from_str "1RB1LC_1LA0RD_1LB0LA_1LB0RE_1RF1RD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm206: halts_at_trans (TM_from_str "1RB0LC_1LA1RD_1RA0LE_1RA0RB_1LF1LC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm207: halts_at_trans (TM_from_str "1RB1RF_1LC---_1LE0LD_1RE1LC_1LD0RF_1LE0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm208: halts_at_trans (TM_from_str "1RB0LB_1RC1LE_1RD0RA_0RE---_1RF0LA_1LB0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm209: halts_at_trans (TM_from_str "1RB---_1LC1RA_0LE0LD_1LB0LF_1RE0LB_1LC0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm210: halts_at_trans (TM_from_str "1RB---_1LC1RA_0LE0LD_1LB0LF_1RE1RB_1LC0LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm211: halts_at_trans (TM_from_str "1RB---_1LC1RA_0LF0LD_1LE0LE_1LC0LC_1RF0LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm212: halts_at_trans (TM_from_str "1RB---_1LC1RA_0LF0LD_1LE0LE_1LC0LC_1RF1RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm213: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_1LD0LC_0RE0LB_1RA1RD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm214: halts_at_trans (TM_from_str "1RB0LC_1LA1LD_1RD0RC_0LB0RE_1RC1LF_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm215: halts_at_trans (TM_from_str "1RB0RC_1LC1RF_1LD0LC_0RE0LB_1RA1RD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm216: halts_at_trans (TM_from_str "1RB---_1LC1RA_1LD0LC_0RE0LB_1RF1RD_0LB0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm217: halts_at_trans (TM_from_str "1RB---_1LC1RA_1LD0LC_0RE0LB_1RF1RD_1RB0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm218: halts_at_trans (TM_from_str "1RB---_1LC1RA_1LD0LC_0RE0LB_1RF1RD_1LE0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm219: halts_at_trans (TM_from_str "1RB0LC_1LC0RF_0LE0LD_1LC---_1LA0RA_1RE1RE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm220: halts_at_trans (TM_from_str "1RB1RB_1LC0RC_1RE0LD_0LB0LF_1LD0RA_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm221: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_1RE0LD_1LA1LA_0RA0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm222: halts_at_trans (TM_from_str "1RB---_1RC0RF_0LD0RB_1LB0LE_1LD1LA_1RD1LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm223: halts_at_trans (TM_from_str "1RB1LC_0RC0LC_0LD1RE_1LB1LF_0RF---_0LA0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm224: halts_at_trans (TM_from_str "1RB1RA_1RC0RF_1LD0RB_1RE0LC_1RA0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm225: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1RE1LD_1RA0RF_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm226: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1RD0LB_1RE1LD_1RA0RF_---0LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm227: halts_at_trans (TM_from_str "1RB0LE_1RC1LB_1RD0RF_1RE0RC_1LA0RD_---0LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm228: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1RD0LB_1RE1LD_1RA1RF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm229: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1RE1LD_1RA1RF_---1RB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm230: halts_at_trans (TM_from_str "1RB0LE_1RC1LB_1RD1RF_1RE0RC_1LA0RD_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm231: halts_at_trans (TM_from_str "1RB---_1LC0RB_0RD1RC_1LA0RE_0RF1RD_1LF1LB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm232: halts_at_trans (TM_from_str "1RB0LC_0RC1RE_1LD0RE_1LA1LF_0RA1RA_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm233: halts_at_trans (TM_from_str "1RB0RF_1LC0LF_0LD0LB_1RE1LB_1RA---_0LD0RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm234: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1RA0LB_1LB0RE_0RF1RB_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm235: halts_at_trans (TM_from_str "1RB0LD_0LC0RB_1RA1LC_0LF1LE_1LA0LC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm236: halts_at_trans (TM_from_str "1RB0LD_0LC0RB_1RA1LC_0LE1LE_1LA0RF_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm237: halts_at_trans (TM_from_str "1RB0RD_1LC0RE_0RD0LC_1LB1RD_0RF1RA_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm238: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_0RD0LC_1LB1RD_0RA1RA_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm239: halts_at_trans (TM_from_str "1RB---_1LC0RE_0RD0LC_1LB1RD_0RA1RF_1RB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm240: halts_at_trans (TM_from_str "1RB1LC_1LA0RC_1LB0RD_1RE1RC_1LF---_0RA1LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm241: halts_at_trans (TM_from_str "1RB1LC_1LA0RC_1LB0RD_1RE1RC_1LF---_1LB1LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm242: halts_at_trans (TM_from_str "1RB0LC_1LA1RC_1RA0LD_1LE1LC_1RF---_1RA1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm243: halts_at_trans (TM_from_str "1RB0LC_1LA1RC_1RA0LD_1LE1LC_1RF---_0LB1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm244: halts_at_trans (TM_from_str "1RB1RE_1LC---_0RD1LB_1RF1LE_1LF0RA_1LD0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm245: halts_at_trans (TM_from_str "1RB1RF_1LC---_1LD1LB_1LE0RF_1RD1LF_1LD0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm246: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1RD0LB_1RE0LD_1RA1RE_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm247: halts_at_trans (TM_from_str "1RB---_1RC0LF_1RD1RA_1LE0RC_0RB0LD_1LB1RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm248: halts_at_trans (TM_from_str "1RB0RF_1RC0LF_0RD1RA_1RE1LF_0LB---_1LB0LD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm249: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1RB1LE_1RA0LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm250: halts_at_trans (TM_from_str "1RB1LE_1LC0RD_1LA0LB_1RB0RE_1RD0LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm251: halts_at_trans (TM_from_str "1RB0LD_1RC0RA_1LA1RE_1LA0LE_1LD0RF_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm252: halts_at_trans (TM_from_str "1RB1RA_1RC1RF_1RD0LE_1LC---_0LF1LE_1RA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm253: halts_at_trans (TM_from_str "1RB0LB_1RC1RF_1RD0LE_1LC---_0LF1LE_1RA0RB") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm254: halts_at_trans (TM_from_str "1RB1LD_1RC---_1LD1RB_0LA0LE_0LA0RF_1RE0RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm255: halts_at_trans (TM_from_str "1RB1LD_1RC---_1LD0RD_0LA0LE_0LA0RF_1RE0RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm256: halts_at_trans (TM_from_str "1RB1LD_1RC---_1LD0RE_0LA0LE_0LA0RF_1RE0RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm257: halts_at_trans (TM_from_str "1RB0LD_0RC0RA_1RD0RF_1LE0LC_1LA0LE_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm258: halts_at_trans (TM_from_str "1RB0LD_0RC0RA_1RD0RF_1LE0LC_1LA0LE_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm259: halts_at_trans (TM_from_str "1RB0LF_1RC0LD_1LD1RE_0RE1LB_0RA---_1LA1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm260: halts_at_trans (TM_from_str "1RB0LE_1LC1RF_1RA0LD_1LC1LC_0RF1LA_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm261: halts_at_trans (TM_from_str "1RB0LD_1RC0LE_1LA1RF_1LA1LA_0RF1LB_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm262: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_0RB1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm263: halts_at_trans (TM_from_str "1RB0LC_0LC1RF_1LE0LD_1LC0RE_1RD0RA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm264: halts_at_trans (TM_from_str "1RB0LC_1RC0RD_1LA0LD_0LE0RA_1RA1LF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm265: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_0RD1LB_1LA0RE_1RD1RF_---1RD") c0 (F,0).
Proof. solve_halt'' 42 true. Time Qed.

Lemma tm266: halts_at_trans (TM_from_str "1RB---_1RC1RF_0RD0RA_1LE0RB_0LF1LB_1RA0LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm267: halts_at_trans (TM_from_str "1RB---_1RC1RF_0RD0RA_1LE0RB_0LF0LD_1RA0LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm268: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1RD0RF_1LE0RD_1LA0LD_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm269: halts_at_trans (TM_from_str "1RB---_1LC0RF_1LF0LD_0RE0LB_1LB1RA_1RB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm270: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LD_0RE0LB_1LB1RF_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm271: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE0RB_1LA0LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm272: halts_at_trans (TM_from_str "1RB0LA_1RC0LE_1RD0RF_1LE0RC_1RA0LD_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm273: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LD---_0LE1RF_1RE0LD_0RA1RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm274: halts_at_trans (TM_from_str "1RB1LC_1RC1RA_0RD0RB_1LE---_0LF0LC_1LA1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm275: halts_at_trans (TM_from_str "1RB1RF_0RC0RA_1LD---_0LE0LB_1LF1LD_1RA1LB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm276: halts_at_trans (TM_from_str "1RB1RF_1LC1RD_1LD1LB_0LE0LC_1RF---_0RA0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm277: halts_at_trans (TM_from_str "1RB---_1RC0RD_1RD0LE_1LC1RB_0LD0LF_1LA1LE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm278: halts_at_trans (TM_from_str "1RB0RF_1LC0LC_1RE1LD_0LB0LC_0RA1RC_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm279: halts_at_trans (TM_from_str "1RB0RF_1LC0LC_1RE1LD_0LB0LC_0RA1RC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm280: halts_at_trans (TM_from_str "1RB0RF_1LC0LC_1RE1LD_0LB0LC_0RA1RC_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm281: halts_at_trans (TM_from_str "1RB---_1LC0LC_1RE1LD_0LB0LC_0RF1RC_1RB0RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm282: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC0LF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm283: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA0RF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm284: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_0RE1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm285: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1LC1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm286: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm287: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_0LE1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm288: halts_at_trans (TM_from_str "1RB1RE_0LC0RF_1RA0LD_1LC1LB_0RA---_0LC0RD") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm289: halts_at_trans (TM_from_str "1RB1RE_1LC0RA_1LE1LD_0LC---_0RB0LF_0RB0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm290: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm291: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LD_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm292: halts_at_trans (TM_from_str "1RB0RD_1LC0LD_1RA0LB_0LE0RC_1RC1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm293: halts_at_trans (TM_from_str "1RB1LC_1LA1RC_1LD0RB_0LE0LF_1RA---_0LA1RE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm294: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE0LD_1LA0LF_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm295: halts_at_trans (TM_from_str "1RB0LA_1RC0RB_1RD0RF_1LE0RC_1RA0LD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm296: halts_at_trans (TM_from_str "1RB0LE_1LC0RA_1LD0RC_1LE0LD_1LA1LF_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm297: halts_at_trans (TM_from_str "1RB0LA_1RC0RB_1RD1RF_1LE0RC_1RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm298: halts_at_trans (TM_from_str "1RB---_1RC0RB_1RD1RA_1LE0RC_1RF0LD_1RB0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm299: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LF_1RA1RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm300: halts_at_trans (TM_from_str "1RB---_1LC0RA_0LD0RD_1RF1LE_0LB1LD_0RE0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm301: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_0LD1LA_1LE0RF_0LA0LD_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm302: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_0LD1LA_1LE0RF_0LA0RA_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm303: halts_at_trans (TM_from_str "1RB---_1LC0RA_0LD0LB_1RE1LF_0RF0RE_0LB1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm304: halts_at_trans (TM_from_str "1RB0RC_0LC0LE_1RD1LC_0RA1RE_1RA1LF_---1LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm305: halts_at_trans (TM_from_str "1RB1RF_1RC0RB_0LD0RA_1LE1RD_0LA0LC_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm306: halts_at_trans (TM_from_str "1RB1LA_1LC0RC_0RA0LD_1LE1LF_1LC0LE_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm307: halts_at_trans (TM_from_str "1RB0RA_1LC0RD_1LD0LB_1RA1RE_1RD0RF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm308: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_1RD0RC_1LE0RB_1LB0LD_---0LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm309: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD0LA_1RE0RF_1LA0RD_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm310: halts_at_trans (TM_from_str "1RB0RD_0RC1RA_1LD0RF_0LE0LD_0RA0LC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm311: halts_at_trans (TM_from_str "1RB0RD_0RC1RA_1LD0RF_0LE0LD_0RA0LC_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm312: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1LB0LC_1RF0LD_1LD1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm313: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm314: halts_at_trans (TM_from_str "1RB0RC_1LC0RE_0RF0LD_1LA0LB_0LC---_1RA1LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm315: halts_at_trans (TM_from_str "1RB1LD_1RC0RF_0RD---_1RE0LF_1LA0LF_1RA0LA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm316: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD1RC_1LF0LE_---0RD_1LA0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm317: halts_at_trans (TM_from_str "1RB0LF_1LC0RA_1LD1RC_1LF0LE_---0RD_1LA0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm318: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD0RB_1LE0RC_1RA0LD_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm319: halts_at_trans (TM_from_str "1RB1LA_1RC0RF_1RD0RB_1LE0RC_1LA0LD_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm320: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD1RC_1LF1LE_---1LA_1LA0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm321: halts_at_trans (TM_from_str "1RB0LF_1LC0RA_1LD1RC_1LF1LE_---1LA_1LA0LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm322: halts_at_trans (TM_from_str "1RB1LA_1RC1RF_1RD0RB_1LE0RC_1RA0LD_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm323: halts_at_trans (TM_from_str "1RB1LA_1RC1RF_1RD0RB_1LE0RC_1LA0LD_---1RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm324: halts_at_trans (TM_from_str "1RB1RB_1LC0RA_1LE0RD_0LC1RC_1RB1LF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm325: halts_at_trans (TM_from_str "1RB1RB_1LC0RA_1LE0RD_0LD1RC_1RB1LF_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm326: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_1LA0RD_0LC1RC_0LB---_1RB1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm327: halts_at_trans (TM_from_str "1RB1LE_1LC0RF_1LA0RD_0LD1RC_0LB---_1RB1RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm328: halts_at_trans (TM_from_str "1RB0LC_1LA---_0LD1LC_1RE0RF_1RF1RE_1RA1RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm329: halts_at_trans (TM_from_str "1RB0LC_1LA---_0LD1LC_1RE0RF_1RF0LF_1RA1RD") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm330: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD0RB_1RE0LC_1RA1LE_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm331: halts_at_trans (TM_from_str "1RB0RF_1RC0RA_1LD0RB_1LE0LC_1RA1LE_---0LA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm332: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD0RB_1RE0LC_1RA1LE_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm333: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD0RB_1LE0LC_1RA1LE_---1RC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm334: halts_at_trans (TM_from_str "1RB0LF_0RC1RD_1LD1RA_0RE1LF_---1RC_1LB0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm335: halts_at_trans (TM_from_str "1RB1RF_1LC1RF_---1LD_1LE0LF_0RA1RC_1RE0LD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm336: halts_at_trans (TM_from_str "1RB0LF_0RC1RE_1RD1RA_1LE1RA_---1LF_1LB0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm337: halts_at_trans (TM_from_str "1RB1LF_0LC1RD_---1LA_1RE0RF_0LA1LB_1LE0RD") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm338: halts_at_trans (TM_from_str "1RB---_0RC1RD_0LD0LA_1LE0RB_0LF1LD_1RA0LA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm339: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_0LC1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm340: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_0LC0RD_0RE---_1LF1RF_1LA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm341: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_0LD1RA_1LE1RB_1RC0LE_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm342: halts_at_trans (TM_from_str "1RB1LE_1LC0RB_0RA1LD_1LE1LA_0LC0LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm343: halts_at_trans (TM_from_str "1RB1LC_1LC0RB_0LF0LD_0LE---_1LC1LA_0RA1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm344: halts_at_trans (TM_from_str "1RB0RF_1LC0RB_0LF0LD_0LE---_1LC1LA_0RA1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm345: halts_at_trans (TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA1RB_1RB1RD_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm346: halts_at_trans (TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0LC_1RB1RD_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm347: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_0LD1RA_1LE1RB_1RB0LE_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm348: halts_at_trans (TM_from_str "1RB1RD_0RC0RF_0LD1RA_1LE0LC_1RB0LE_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm349: halts_at_trans (TM_from_str "1RB0LA_0LC1RE_1LA1RD_0RB0RF_1RD1RC_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm350: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_0LA0RA_0LE1LA_1LC0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm351: halts_at_trans (TM_from_str "1RB1LD_1RC---_1RD0RF_1LE0LF_0LA0LD_0LA0RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm352: halts_at_trans (TM_from_str "1RB0LC_1RC1RA_0RD0LE_1LE1RF_1LB1LC_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm353: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1RD0LB_1RE0LD_1RA0LC_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm354: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_0LD1LB_1LA0LF_0RA0RB_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm355: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_0LD1LB_1LA0LF_0RA0RB_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm356: halts_at_trans (TM_from_str "1RB0RB_1LC1RE_0LD1LB_1LA0LF_0RA0RB_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm357: halts_at_trans (TM_from_str "1RB1RF_1RC0RA_1LD0RB_0LE0LC_0LA1LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm358: halts_at_trans (TM_from_str "1RB0LC_1LC1RF_1LE0LD_1LC0RE_1RD0RA_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm359: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_1LC1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm360: halts_at_trans (TM_from_str "1RB0LE_0RC0RF_1RD0LD_1LA0RB_1LC1LC_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm361: halts_at_trans (TM_from_str "1RB---_0RC0RA_1RD0LD_1LE0RB_1RB0LF_1LC1LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm362: halts_at_trans (TM_from_str "1RB0LB_0LC0RD_1LA1LD_1RE0LF_0RB0LB_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm363: halts_at_trans (TM_from_str "1RB0LF_0RC0LC_0LD0RA_1LE1LA_1RC0LC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm364: halts_at_trans (TM_from_str "1RB---_0RC1LB_1RD1LE_1RE0LB_0LD1RF_1RA0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm365: halts_at_trans (TM_from_str "1RB1LC_1RC0LD_0LB1RE_0RA1LD_1RF0LE_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm366: halts_at_trans (TM_from_str "1RB0LC_0LA1RE_0RD1LC_1RA1LB_1RF0LE_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm367: halts_at_trans (TM_from_str "1RB0LF_0RC0LC_1LD1RE_1LB0LD_0RA1RC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm368: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1LD0LB_0RD0LE_0LF---_1RA1LA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm369: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_0RD0RE_1LE0RF_1LA0LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm370: halts_at_trans (TM_from_str "1RB0LA_1RC0RA_1LD0RB_0LE0LC_1LA0LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm371: halts_at_trans (TM_from_str "1RB---_1LC0LF_1RD0LB_0RE0RC_1RF0RA_1LB0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm372: halts_at_trans (TM_from_str "1RB0LE_1RC0LB_1RD0RF_1RE1RB_1LA0RD_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm373: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RD0LB_1RE0LD_1RA0RF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm374: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RD0LB_1RE0LD_1RA1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm375: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RD0LB_1RE0LD_1RA1RF_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm376: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1RD0LB_1RE0LD_0LE1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm377: halts_at_trans (TM_from_str "1RB0LC_1LA1RF_1LD0LE_1RE0RA_1LC0RD_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm378: halts_at_trans (TM_from_str "1RB---_1LC0RA_0LD0RD_1RF1LE_0LB1LD_1RC0RF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm379: halts_at_trans (TM_from_str "1RB0RA_0LC0RC_1RA1LD_0LE1LC_1LB0RF_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm380: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RE_0LF0LC_1RC1RA_1RA0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm381: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RE_0LF0LC_1RC0RD_1RA0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm382: halts_at_trans (TM_from_str "1RB0RF_0RC0RA_1LD1RA_1LE---_1LA0LF_0RC0LD") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm383: halts_at_trans (TM_from_str "1RB0LA_1RC---_1RD0RB_1LE0RF_0LA0LD_1RD1RB") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm384: halts_at_trans (TM_from_str "1RB0LA_1RC---_1RD0RB_1LE0RF_0LA0LD_1RD0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm385: halts_at_trans (TM_from_str "1RB1LF_1RC0RD_1LD0LE_1RB0LC_1LA0RB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm386: halts_at_trans (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm387: halts_at_trans (TM_from_str "1RB0RF_1RC0RE_1LD0RB_1LB0LC_1RA0LD_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm388: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB0LF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm389: halts_at_trans (TM_from_str "1RB1RF_1RC0RE_1LD0RB_1LB0LC_1RA0LD_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm390: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1LB0LC_1RF0LD_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm391: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1LB0LC_1RF0LD_0LF1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm392: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm393: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_0RE1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm394: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LB_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm395: halts_at_trans (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_0RA1RF_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm396: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0RB_1LB0LC_1RF0LD_0LD1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm397: halts_at_trans (TM_from_str "1RB0RC_1LC0LD_1RA0LB_1LE0RA_0RA1LF_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm398: halts_at_trans (TM_from_str "1RB0LE_0RC1LD_1RD1RF_0LB1RA_1LA1LB_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm399: halts_at_trans (TM_from_str "1RB1RE_1RC0LD_1LB---_0LE1LD_1RF0RA_1RA0LA") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm400: halts_at_trans (TM_from_str "1RB1RE_1RC0LD_1LB---_0LE1LD_1RF0RA_1RA1RF") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm401: halts_at_trans (TM_from_str "1RB1RF_1LC0LE_1RD0LB_0RE0RC_0LA0RA_1RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm402: halts_at_trans (TM_from_str "1RB---_1LC0LE_1RD0LB_0RE0RC_0LF0RF_1RB1RA") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm403: halts_at_trans (TM_from_str "1RB---_1RC0RE_1LD0LE_0LF0LC_0LF0RA_1RA1LC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm404: halts_at_trans (TM_from_str "1RB0LA_1RC---_0RD1LC_1RE1LF_1RF0LC_0LE1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm405: halts_at_trans (TM_from_str "1RB0RC_1RC1RB_1RD1RA_1RE0LF_1LD---_0LA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm406: halts_at_trans (TM_from_str "1RB0RC_1RC0LC_1RD1RA_1RE0LF_1LD---_0LA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm407: halts_at_trans (TM_from_str "1RB1LF_1LC0RD_1LA1LD_1LB0RE_0LA1RB_0LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm408: halts_at_trans (TM_from_str "1RB0LF_1RC0RA_0LC1LD_1LE0RD_1LF---_1LA0LE") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm409: halts_at_trans (TM_from_str "1RB0LA_1RC---_1RD0RB_1LE0RC_1LF0LD_0RF1RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm410: halts_at_trans (TM_from_str "1RB0LF_0RC0RD_1LD1RE_0LE0LD_0RA1RC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm411: halts_at_trans (TM_from_str "1RB0RF_0LB1LC_1LD0RC_1LE---_1LF0LD_1RA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm412: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1LD0LB_0RD1RE_1RF0LE_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm413: halts_at_trans (TM_from_str "1RB0LB_0RC1LB_1RD0LA_1LE1LF_1LA0LD_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm414: halts_at_trans (TM_from_str "1RB0LF_1LC0RA_0RD1LB_1RF1RE_---1RF_1LA0RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm415: halts_at_trans (TM_from_str "1RB0LA_1RC1LE_1LD0RF_---1LE_1LB0LB_0RD0RA") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm416: halts_at_trans (TM_from_str "1RB0LA_1RC1LD_1LB0RE_1LB0LB_0RF0RA_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm417: halts_at_trans (TM_from_str "1RB0LA_1RC1LD_1LB0RE_1LB0LB_0RF0RA_---0RD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm418: halts_at_trans (TM_from_str "1RB0LA_1RC1LD_1LB0RE_1LB0LB_0RF0RA_---1LD") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm419: halts_at_trans (TM_from_str "1RB0LA_1RC1LD_1LB0RF_0RE0LB_---1LC_0RE0RA") c0 (E,0).
Proof. solve_halt. Time Qed.



