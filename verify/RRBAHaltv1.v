From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
Module RRBA62 := RRBA BB62.
Export RRBA62.
Require Import NArith.
Require Import String.


Ltac solve_halt' T1 T2 :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 ?tr =>
    idtac x;
    apply (decide_halt_spec' _ T1 T2 tr);
    native_cast_no_check (eq_refl (Some tr))
  end.

Ltac solve_halt :=
  solve_halt' 50000%N 10000%N.

Notation "'F'" := BB62.F.

Lemma tm1: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LF1LE_1RE0LA_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_0RF1RD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1RF_1LC0RE_0RB1LD_1LB0LD_---0RA_1RD1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB0LE_0LC0RE_1LA0RD_1LB0RB_0RD1LF_0LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB---_1RC0RB_1LD0LF_1RB1LE_1LC0LD_1LA1RB") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB1LE_1RC1RD_1RD1RF_1LA1RA_---0LF_0RA0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LF_0RC0RB_1LD0LA_1LE---_1LA1RE_1LC0LA") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RF0RD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_1LF1LA_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_0LA0RF_1RA0RB_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB1LF_1RC0RB_0LD0RD_---0RE_1LE1RA_1LA0LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB---_1RC0RD_1RD0RA_1LE1RB_0LF0LE_1RF0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RD_1RC---_1LD0RF_1RA0LE_0LD1RC_0RC0RE") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB1LA_1RC0RB_1LD1RC_1LF1LE_1LB0LD_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB---_1LC1RE_0LD0LC_1RD0RB_1RA1RF_0RB1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0LF_0RC---_1RD0LA_1RE1RC_1LF1RB_0RA0LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LF_1LC0RE_1LD0LB_1LA---_0RB1LA_0LA0LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_0RF1RD_0LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB0RA_1LC1RB_1LE1LD_1LA0LC_1RF---_1RA1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB---_1RC0RF_1RD1LB_1RE0RD_1LF1RA_1LC0LF") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---1RF_0RC0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_0LF1RB_0RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB0RE_1LC1RF_0LD0LC_1RE0RB_1RF---_1RA0RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB1RC_1LC1RF_1RD0LC_0LE0RE_1RA1LD_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0LC_0RC1RA_1LD0RE_1RA0LD_1RF---_1LA0RC") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB0LF_0RC---_1RD0LA_1RE1RC_1LF1RB_0RE0LC") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1LE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0RF_1LC1LF_1RD1LC_---1RE_1RD1RF_1RA0LB") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB---_1LC1RE_0LD0LC_1RD0RB_1RA0RF_1LD1RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB1LB_1RC0RD_0LD1RB_0RA1RE_1LF---_1LC0LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB1LF_1LC1RD_0LD0LC_1RE0RA_1RF---_1RA0RB") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_0LF1LA_0RB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1RD1RF_1LE0LA_1LA0LC_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB0LE_1RC0RA_1RD---_1LA0RF_0LA1RD_0RD0RE") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1RF0LA_1LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB1LE_1RC1LC_1LD0RC_0LA0RB_---1LF_0LD0LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB1LF_1RC1LB_0RD1RD_1LE0RC_0LE1LA_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB0LD_1LC0RB_1LD1RC_0LA1LE_0LF1LA_1LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_1RC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB0RF_1RC1LB_0RD1RD_1LE0RC_0LE1LA_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0RB1LE_---1LF_1LC0LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1LA_0RC1RC_1LD0RB_0LD1LE_1RA0RF_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB0LC_1LC0RB_1LE1LD_1LA0RD_0LF---_1RD1LF") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB---_1LC0RF_1RE0LD_0LC1RB_1RA0RC_0RB0RD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB0RD_1RC1RF_0LD---_1RE1LE_1LA0LE_1RA0RB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_1RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1RF1RA_1LA1LF") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB0RA_0RC0LD_1LD1RF_1LE1LD_1LB1RE_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_0RF1RA_0RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_0RF1RC_0LB---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB---_1LC1RE_1LD0LC_1RE1LD_1RA1RF_1RD0RE") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB---_1RC1LB_1LD1RE_1LB0LD_1RA1RF_1LF0RC") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LC_1RE0LF_---1RA_0LC1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB0LD_1LC0RD_0LD1LB_1RE0LF_1LB0RE_1LA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LC_1RE0LF_---1RA_0LC1RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB0RA_0LC0RF_0LD1LD_1LE1LD_1RF0LC_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RF_1RA0RB_0RD---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0RA_0LC0RF_0LD1RC_1LE1LD_1RF0LC_---1RA") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB1LA_1RC1RD_1LA---_1RF0LE_0LD1LE_0RF1RB") c0 (C,1).
Proof. solve_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB0RA_0LC0RE_1LD1LC_1RE0LF_---1RA_0LC1LC") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB0RB_1RC1RF_1LD0RA_1LA1LE_1LC0LE_---1RA") c0 (F,0).
Proof. solve_halt' 500000%N 10000%N. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB1RE_1LC1LB_1LD1RC_0RA0LB_---1RF_1RD0RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB0LC_1LC0RD_1LE0LD_0RB1LA_1LA1LF_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB1RD_0LC0RE_1RA1LC_0LB1RF_1LD---_0RD0RA") c0 (E,1).
Proof. solve_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB1RA_1LC1RD_1LA1LC_---1RE_0LF0RB_0LA1LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB1LA_0RC1RC_1LD0RB_0LD1LE_1RA1RF_---0RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1RA---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB1LD_1RC0RB_1LA1LE_1LC0LA_0LF0RD_1LC---") c0 (F,1).
Proof. solve_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_0RD1LD") c0 (A,1).
Proof. solve_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0RC_0RC0RF_0LD1RA_1LE---_0LA1LF_1RC1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1LE1LD_1RE0LC_---1RA_1RA0LE") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB1RA_0LB0RC_1LD0LE_1LE---_0RA1LF_1RF0LC") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB1LF_1LC0RE_1LD1LB_1RB1RD_0LA1RE_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB1LA_1LC1RC_1LE1RD_0RF0RB_0LA1LE_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB1LA_1LC1RC_1LE1RD_0RE0RB_---1LF_0LA1LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0LB_1LC1RB_---1LD_1RC1LE_1LA0RF_0LD1RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_1RD1LC_---1RE_1RA1RA_0RE1LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB1RA_1LC0RE_0RE1LD_1LA0LF_1LF1RE_---1LC") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1LE1LD_1RE0LC_---1RA_1RA1RB") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB0LB_1LC1RB_---1LD_1LE1LE_1LA0RF_0LD1RF") c0 (C,0).
Proof. solve_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB1LF_1LC1RD_1LC1LA_---1RE_0LA0RB_0LA0RD") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB1RE_1LC1RB_0RA1LD_1LC0LC_---1RF_1LF0RA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB0RC_1RC---_0LD1RF_1LE1LD_0RE0LA_1LF0RA") c0 (B,1).
Proof. solve_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1LE_1LC1LB_0RD1RC_1LA1RD_---1LF_0RD0LA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB1RE_1LC0LF_0RA1LD_1LC0LC_---0RB_1RC1RA") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB1LA_0LC1RF_1LA1LD_0RE0RB_---1LB_1LE1RD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB1LA_1LC1RC_1LE1RD_0RE0RB_---1LF_0LA1LD") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LA_1LC1RC_1LE1RD_0RF0RB_0LA1LE_---1RE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB0RC_1LC0RF_0LD1RA_1LE---_0LA1LF_1RC1LE") c0 (D,1).
Proof. solve_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1LA_1LC1RC_1LE1RD_0RE0RB_---1RF_0LA1LF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1LA_0LA1RC_0RD0RB_1RE0RE_1LF0LB_---1LE") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB1RA_1LC0RD_1LA1LB_0LE1RD_1RB1LF_---0LB") c0 (F,0).
Proof. solve_halt. Time Qed.

Lemma tm103: halts_at_trans (TM_from_str "1RB1RA_1LC0RE_0RF1LD_1LA0LE_---1LC_1LE1RF") c0 (E,0).
Proof. solve_halt. Time Qed.

Lemma tm104: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_1RD1LC_---1RE_1LD1RA_0RE1LF") c0 (D,0).
Proof. solve_halt. Time Qed.

Lemma tm105: halts_at_trans (TM_from_str "1RB0RB_1LC1RF_1LE1LD_1RE0LC_---0LB_1RA1RB") c0 (E,0).
Proof. solve_halt. Time Qed.

