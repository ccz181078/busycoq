From BusyCoq Require Import Inductive62.

Ltac native_check_eq :=
match goal with
| |- _ = ?a => native_cast_no_check (eq_refl a)
end.

Ltac solve_hlin_halt_T T :=
  apply (decide_hlin_halt_spec default_config T);
  [ apply Config_WF_simple; reflexivity
  | native_check_eq ].

Ltac solve_hlin_halt :=
  match goal with
  | |- halts_at_trans (TM_from_str ?x) c0 _ =>
    idtac x;
    solve_hlin_halt_T 1000000%N
  end.

Lemma tm1: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_0RE1LD_0LB0LC_1RA0LE_---0RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm2: halts_at_trans (TM_from_str "1RB---_1RC0LF_0RD1RF_1RE0LE_1LB1RA_1LD0RB") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm3: halts_at_trans (TM_from_str "1RB0LE_1LC0RC_1RE1LD_1LE---_1LF0RA_0LB1LA") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm4: halts_at_trans (TM_from_str "1RB1RE_1RC1RA_1LD0RE_0LF1LC_0RC0LC_1RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm5: halts_at_trans (TM_from_str "1RB1LF_1LC0RD_0LE1LD_1RE0LB_1LA0RA_1LB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm6: halts_at_trans (TM_from_str "1RB0RF_0RC0LD_1LA0RE_0LE1LB_1RC0RA_---1LC") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm7: halts_at_trans (TM_from_str "1RB1RD_0LC---_1RD1RC_1LE0RF_1RC0LD_1LD0RA") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm8: halts_at_trans (TM_from_str "1RB---_0RC0LE_1LD0RF_1RB1LD_0LF1LB_1RC0RA") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm9: halts_at_trans (TM_from_str "1RB0RC_1LC1LB_1RD1LD_0LE0RA_0RC1LF_0LB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm10: halts_at_trans (TM_from_str "1RB0LF_1LC0RC_1RE0LD_0LB0LE_1LD0RA_1LA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm11: halts_at_trans (TM_from_str "1RB0LC_0RC1RF_1LD1RA_0LE0LA_0RB0LD_0RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm12: halts_at_trans (TM_from_str "1RB1LD_0RC0RD_1LA0RB_1LE0RA_0LA1LF_0LD---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm13: halts_at_trans (TM_from_str "1RB1RF_1RC0RB_1LD0RA_0RF0LE_0LD0LB_0RB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm14: halts_at_trans (TM_from_str "1RB0LB_1RC---_0RD1RE_0LE0LB_1LF0RC_0LA1LE") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm15: halts_at_trans (TM_from_str "1RB0LE_1LC0LF_0LA0RD_0RE1RC_1LA0LB_---1RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm16: halts_at_trans (TM_from_str "1RB---_0RC0RD_1LC1LD_1RB0LE_0LF0LA_1LD0RE") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm17: halts_at_trans (TM_from_str "1RB1RF_0LC0LD_1RA1RD_1LB0RE_0RC---_0RA1RC") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm18: halts_at_trans (TM_from_str "1RB1LC_1RC0RF_1LA0LD_0LE0LA_1RC0RA_---0RE") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm19: halts_at_trans (TM_from_str "1RB0LE_1LC1RB_0LA0RD_0RE1RC_1LA0LF_1LC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm20: halts_at_trans (TM_from_str "1RB1RD_1LC0LD_1RF1LD_1RE0LC_1RC0RA_1RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm21: halts_at_trans (TM_from_str "1RB1RE_0RC---_1RD0LE_1RE1RD_1LC0RF_1LE0RA") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm22: halts_at_trans (TM_from_str "1RB0RD_1LC1RF_0LD0LB_0RE0LB_0RF---_0RB1RA") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm23: halts_at_trans (TM_from_str "1RB0RB_1RC1RA_1LD1LE_---1LC_0LF0LB_1RF0LB") c0 (D,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm24: halts_at_trans (TM_from_str "1RB0LC_1RC1RB_1LA0RD_1LC0RE_1RF1RC_0LB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm25: halts_at_trans (TM_from_str "1RB1RF_1LC0RE_0LE0RD_---0RB_1LF0LC_1RA1LC") c0 (D,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm26: halts_at_trans (TM_from_str "1RB0LE_0RC1RE_1RD0LD_1LA1RF_1LC0RA_1RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm27: halts_at_trans (TM_from_str "1RB0LD_0RC1RF_1RD0RF_1RE1LA_1LD---_0LF1RA") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm28: halts_at_trans (TM_from_str "1RB0LE_1RC1RF_1LD0RA_0LA1LE_0LC1LC_---0LE") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm29: halts_at_trans (TM_from_str "1RB1RC_1RC---_1LD0RE_1RF0LC_1LC0RA_1RC1RF") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm30: halts_at_trans (TM_from_str "1RB0RF_0LC1LB_1LD1LA_1RE0LC_0LA0RD_0RE---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm31: halts_at_trans (TM_from_str "1RB---_1RC1RE_0LD0RB_1LF1LC_0RC1RA_1LA1LC") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm32: halts_at_trans (TM_from_str "1RB0RF_1LC0RA_1RD1LC_0RB0LE_0LA1LD_1RD---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm33: halts_at_trans (TM_from_str "1RB0RF_1RC1RA_0LD0RA_1LF0LE_---1LD_0LA1LC") c0 (E,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm34: halts_at_trans (TM_from_str "1RB---_1RC0RA_1LD0RB_0LE0LC_1RA0LF_1RF0LE") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm35: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_1RE1LD_0LB0LC_1LF0LA_---0RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm36: halts_at_trans (TM_from_str "1RB0RB_1LC0RA_0LE1LD_1LE---_1LA0LF_1LC1RE") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm37: halts_at_trans (TM_from_str "1RB1RE_1LC---_1LE1LD_0LE1LB_0RF0LC_1RA1RE") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm38: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_1LA1LD_1LE---_0LB1LC_1LD0RA") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm39: halts_at_trans (TM_from_str "1RB0RB_1LC1LF_0LE0LD_1LC0RA_1RE1RD_---0RE") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm40: halts_at_trans (TM_from_str "1RB0LD_0RC1RE_1RD0RF_1LA0LA_1RC---_1RB1LC") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm41: halts_at_trans (TM_from_str "1RB1LA_0RC0LD_1LA0RE_0LE1LB_1RC0RF_1RB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm42: halts_at_trans (TM_from_str "1RB0RE_0LC1LE_0RD1LD_1RA---_1LF0RA_0LB0LA") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm43: halts_at_trans (TM_from_str "1RB0LC_1RC1RB_1LA0RD_1LC0RE_0RF1RC_0LC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm44: halts_at_trans (TM_from_str "1RB1RA_1RC0LF_1LD0RE_1LB0LD_1RA---_0RF1RD") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm45: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_---1LD_1RD1LB_1RA1LF_0LE0LA") c0 (C,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm46: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_0LD1RE_1LA0RA_0LD1LE_0RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm47: halts_at_trans (TM_from_str "1RB1RF_1LC0RE_0LE1LD_0LB1LB_1RA0LD_---0LD") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm48: halts_at_trans (TM_from_str "1RB0LB_0RC1LF_1RD1RC_0LE0RD_0LA1LA_---1LE") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm49: halts_at_trans (TM_from_str "1RB1LE_1LC1RF_1RA0LD_0RB0LB_---0LC_0RA1RC") c0 (E,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm50: halts_at_trans (TM_from_str "1RB0LF_0LC0RA_1RE0RD_0RB---_0LF1LE_1LA1LC") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm51: halts_at_trans (TM_from_str "1RB1LA_0RC0LB_1LD---_1RE0RB_1RF1RD_1LA0RE") c0 (C,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm52: halts_at_trans (TM_from_str "1RB0LB_1LC1RE_1RF0LD_1LA0RC_1RC---_0RA1RD") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm53: halts_at_trans (TM_from_str "1RB1LC_1LC1RD_0LE1LD_0RA1RE_1RA0LF_---0LB") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm54: halts_at_trans (TM_from_str "1RB---_1RC1RB_1RD0LF_1LE0RA_1LC0LE_0RF1RE") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm55: halts_at_trans (TM_from_str "1RB---_1RC0RB_1LD0RA_0LE0LC_1RA0LF_1RF0LE") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm56: halts_at_trans (TM_from_str "1RB1RD_1LC0RA_0RD0LB_1LF0LE_0LC---_0RA1RF") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm57: halts_at_trans (TM_from_str "1RB0LE_1RC0LA_1LD0RB_1LB1LD_0LF1LB_0RB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm58: halts_at_trans (TM_from_str "1RB1RD_1RC1RF_0LA0LD_1LC0RE_0RA---_0RB1RA") c0 (E,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm59: halts_at_trans (TM_from_str "1RB1LC_1LA---_1RD0LA_0RF1RE_0LE1RC_1RA0RE") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm60: halts_at_trans (TM_from_str "1RB1LE_0RC0RA_0LD0RA_0LE---_0LA1LF_1LA1LC") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm61: halts_at_trans (TM_from_str "1RB0LC_1LC1RD_0LA0LD_1RE0LB_0RB1RF_0RD---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm62: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_1LE1LD_1LC0LF_1RB1LA_0LA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm63: halts_at_trans (TM_from_str "1RB0LF_1RC---_1RD0RB_1LE0RC_0LA0LD_1RF0LA") c0 (B,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm64: halts_at_trans (TM_from_str "1RB0RE_1LC1RA_---1LD_1RA1LB_1RA1LF_0LE0LA") c0 (C,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm65: halts_at_trans (TM_from_str "1RB1LC_0RC1RF_1RD0RA_1LE0LE_1RB0LD_1RC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm66: halts_at_trans (TM_from_str "1RB0LD_1LC0RA_1LA1LC_1RA0LE_0LF1LA_0RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm67: halts_at_trans (TM_from_str "1RB1RE_1LC0RD_---0LD_0LE0LF_1RA0RE_0RE1LC") c0 (C,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm68: halts_at_trans (TM_from_str "1RB0LC_1RC1RB_1LA0RD_1LC0RE_1RF1RC_1RC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm69: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_1LA0RD_0RF1RC_1LC0RA_---0RB") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm70: halts_at_trans (TM_from_str "1RB1LE_1LC0RE_1LA1LD_1LC0LF_1RB0RA_0LE---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm71: halts_at_trans (TM_from_str "1RB0LF_1LC1RF_---0LD_1LE0LA_1LA1LC_1RA0RF") c0 (C,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm72: halts_at_trans (TM_from_str "1RB1LF_1RC0LF_1RD0RC_1LE0RB_0LA0LD_1LD---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm73: halts_at_trans (TM_from_str "1RB0LC_1RC1RB_1LA0RD_1LC0RE_1RF1RC_0RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm74: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0RB0LD_0LC0LA_1RA0RF_1RC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm75: halts_at_trans (TM_from_str "1RB0RC_1LC0RA_1RE0RD_---1LB_0RB0LF_0LA1LE") c0 (D,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm76: halts_at_trans (TM_from_str "1RB---_1LC1RF_0LE0LD_0RB0LB_1RA0LD_0RA1RE") c0 (A,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm77: halts_at_trans (TM_from_str "1RB0LC_0RC0LF_1RD0RB_1LE1RB_1LA1LD_---0LA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm78: halts_at_trans (TM_from_str "1RB0LB_1LC0RF_0LE1LD_0LB---_0RA1LF_0RA1RF") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm79: halts_at_trans (TM_from_str "1RB1RE_1LC0RD_---0LD_0LE0LF_1RA0RE_1RD1LC") c0 (C,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm80: halts_at_trans (TM_from_str "1RB0LC_1RC1RB_1LA0RD_1LC0RE_0RF1RC_0LA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm81: halts_at_trans (TM_from_str "1RB0RC_1RC1RF_1LD0RE_1RF1LE_1LC0LE_---0RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm82: halts_at_trans (TM_from_str "1RB0LE_0RC1RF_0LD1RC_1LA0RA_0LD1LE_0RA---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm83: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1LD0RF_1LE---_1LA0LD_1LF0RC") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm84: halts_at_trans (TM_from_str "1RB1LD_1RC1RA_1LD0RF_0LF0RE_---0RC_1LA0LD") c0 (E,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm85: halts_at_trans (TM_from_str "1RB0RE_1LC0RA_0LF0RD_---1RE_0RC1LB_1LA0LB") c0 (D,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm86: halts_at_trans (TM_from_str "1RB0LC_1LC0RF_0LE0LD_1LC---_1LA0RA_1RE1LC") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm87: halts_at_trans (TM_from_str "1RB1RA_1LC0LF_1RE1LD_0LB0LC_1LF1RB_---0RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm88: halts_at_trans (TM_from_str "1RB0LE_0RC0RA_1RD0LD_1LA0RB_1LC0RF_1RE---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm89: halts_at_trans (TM_from_str "1RB0LB_1LC0RE_1RE0LD_1LA0RF_0RA0RC_1RD---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm90: halts_at_trans (TM_from_str "1RB0LF_0LC0RE_1LD0RD_1LA1LC_0RB1RB_0LB---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm91: halts_at_trans (TM_from_str "1RB0RF_0RC1RE_1LD0LB_1LE1LC_0RA0LC_---1RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm92: halts_at_trans (TM_from_str "1RB1RD_1LC0LC_1LD1LB_1RA1RE_0RF0RC_---1LB") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm93: halts_at_trans (TM_from_str "1RB1LB_0LC0RF_0RA1LD_0LE---_1LA1LE_1RE0RA") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm94: halts_at_trans (TM_from_str "1RB1LA_1RC0LB_1RD---_1RE0RB_1RF1RD_1LA0RE") c0 (C,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm95: halts_at_trans (TM_from_str "1RB0RE_1LC0RF_1LA1LD_1LE---_0LB1LC_1RE0RA") c0 (D,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm96: halts_at_trans (TM_from_str "1RB0RA_1LC0RE_0RB0LD_0LC0LA_1RA1RF_1RC---") c0 (F,1).
Proof. solve_hlin_halt. Time Qed.

Lemma tm97: halts_at_trans (TM_from_str "1RB0LE_1LC1RA_1RE1LD_1LA1LF_1LA0RC_---0LC") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm98: halts_at_trans (TM_from_str "1RB1LF_1LC0RA_1RD0LB_1LE1RC_---0LA_1LC1LE") c0 (E,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm99: halts_at_trans (TM_from_str "1RB0LD_1RC1LB_0LA1RF_1LA0RE_1RD1LC_---0RA") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm100: halts_at_trans (TM_from_str "1RB1LE_1LC0RA_1RD0LB_1RE1LD_0LC1RF_---0RC") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm101: halts_at_trans (TM_from_str "1RB1RF_1RC0LC_1LD1LC_1RE1LB_---0RA_0LD0RE") c0 (E,0).
Proof. solve_hlin_halt. Time Qed.

Lemma tm102: halts_at_trans (TM_from_str "1RB1LE_0RC1RA_1RD0RA_1LA1RE_1LC0RF_---0LD") c0 (F,0).
Proof. solve_hlin_halt. Time Qed.

