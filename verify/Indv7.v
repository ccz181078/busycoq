From BusyCoq Require Import Inductive62.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec default_config T);
  [ apply Config_WF_simple; reflexivity
  | native_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    solve_hlin_nonhalt_T 1000000%N
  end.


Lemma tm1: ~halts (TM_from_str "1RB0LD_1RC0LF_1RD0LC_1RE---_1RF0RA_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB---_0RC0RA_1RD0RE_1LE0RF_0LF0LE_1RB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0RE_0RC1LC_0LD1LE_1LE0LF_1RA0LB_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1RF_0RC1RF_1LD0RA_0LE0RE_1RA0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1RC_1LA1RF_0LB0RD_1LE1RD_0LE0RC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD0LB_1RA0LE_1RA0RF_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB1RA_1LC1RD_1LD0LC_0RB0RE_---1RF_1RF1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD0RA_0LE0RE_1RA0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0RE_1LC0RA_1LA0LD_0LB1LF_1LA1RC_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0LD_1RC1RC_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB1RF_1LC0LE_---0LD_1RA1LF_0LC0RD_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0LD_1RC0LF_1LA1RE_0LA1LD_0RB0RA_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB---_1RC0LF_1RD0LE_1LC0RF_0LB0LD_1RC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0LA_0LC0RD_1LA1LC_0RE1RD_1RA1RF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0LF_1RC1LA_0RD---_1RE1RA_0LB0LE_1LE0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB0RD_1LC0RF_1RA0LD_1RC1LE_0LC1LC_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0RD_0RC1RF_1LD0RA_0LE0RE_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0LF_1LC0RA_1LA1LD_0LE0LB_0LC1LE_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE1LE_1RC1LF_0LC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB0RD_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB0RB_1RC1RF_1LD1RB_1RD0LE_0LD0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB1RF_0RC0RD_1LD0RA_0LE0RE_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB1RA_1LC0LF_0RA0LD_0LB0LE_0RB---_1LB1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB1RA_1LC0LF_0RA0LD_0LB1LE_0RA---_1LB1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB1RC_1RC0LB_0LD0RE_1LB1LD_---1RF_0RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB---_1RC0LC_0RD0LD_1RE0LB_0RF1RA_1LF1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB---_1RC0RC_1RD1RA_1LE1RC_1RE0LF_0LE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1RB_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB1RF_1RC0LB_0LD0RE_1LB1LD_0RA1RE_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB0LC_1RC0RA_1RD1RF_1LD0LE_---0LF_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0RF_1RC0LD_1LB0RA_0LE0LC_1RB0LA_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB1LE_0LC0RB_0RA1LD_0LE---_1LA0LF_1LE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB---_1LC0RF_1LF1LD_0LE0LB_0LC1LE_1RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB0LE_1RC0LD_1LB0RE_0LA0LC_1RB0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB1LD_1LC0RE_1LA0RD_0LB0LE_0RB0LF_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1RA_1LC0LF_0RD0LD_0LB1LE_0RA---_1LB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB---_1RC0LD_1RD0RB_0RE1LE_0LF1LB_1LB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB0RE_1LB1RC_0RF0LD_1LE0LD_0RB0LA_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB1LC_0LC0RF_1RC1LD_0LE1RF_1LB---_0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB---_0RC1RA_1RD0LE_1RE0RB_1LC0LF_1RE1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB0RA_0RC0RF_1LD0RC_0LE---_1RA0LF_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0LD_1RC0RD_1LA0RF_1RA1LE_0LA1LA_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB---_1LC0LF_1RF0LD_1LE0RB_0LB0LA_0RD0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB0LA_1LC0RC_1RD1LA_1RA0RE_---0RF_0RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB0LF_0LC---_1LD1LC_0RE0LA_0RF1RE_1RA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0RA_0LC0RF_1RC1LD_0LE1RF_1LB---_0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB0RF_1RC0LB_0LD0RE_1LB1LD_0RA1RE_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB1RC_0LC0RA_1RE0LD_1LC1LA_1RD0RF_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0LC_1RC0RF_1LA1LD_1RE1RA_0LA0RD_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---0RF_0RC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB1RE_1RC0LB_0LD1LA_1LB1LD_---0RF_0RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB1RA_1LC1RD_1LD0LC_0RB0RE_---1RF_1RF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD1LD_1RE0RA_1LA1LE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD---_0LB1LA_1RB0RF_1RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB0RD_1RC0RA_1LD0RE_0LF0LE_1LC0LB_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB0RF_1RC0LB_0LD0RE_1LB1LD_0RA1RE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0LB_0LC1LE_1LE0RD_1RC0RA_1RC1LF_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB0LA_1LC0RD_1LD0LB_0RE1LA_1RF1RB_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB1RF_0RC0RE_1LD---_1LE0LA_1RA0LD_0RA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB1RF_1LC0RA_1LD0LC_1RE0LB_0RB0RD_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB---_1LC0RD_0LD1LA_1LF0LE_0RB0RE_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB1LB_1RC0LF_1RD1RA_0LE0RB_---1LF_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0LB_0LA0LE_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0RE_1LA1LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB---_0RC0LE_1LD0LB_1RE0RB_1LC1RF_0RE1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB0RD_0LC1RE_1LF1LD_1RA0LB_1LD0RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB1LD_1LC0RF_1LE1RD_0LB0RC_1LA---_0RD1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB---_1RC0LA_1RD0RB_1LE0RC_0LF0LD_0LB1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB1LC_1RC0RE_1RD0LC_1LA0RA_---0RF_0RC1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB1LE_1LC1RD_1LD0LC_0RB0RE_---1RF_1RF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1RF_1LC1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0LA_0LC0RD_1LA1LC_---1RE_0RF1RE_1RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB0RD_0LC1RE_1LF1LD_1RA0LB_1LD0RE_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB---_0LC0LA_1LF0LD_0RE0RD_1LB0RC_1RD0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA1LA_0RB0LE_1RD---_0LB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB0RF_1LC0RA_1RB1LD_0LE---_0LB1LC_1RE0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB0RF_1LC0RA_1LD0LC_1RE0LB_0RB0RD_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1RF_1LC0RA_1LD0LC_1RE0LB_0RB0LA_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_1LA1LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB1LF_1RC---_1LD1RF_1RA0LE_0LF1LE_0RD0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB0RF_1LC0RD_1LD0LB_0LE1RE_0RA1RB_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_0LB---_1LF1LB_0RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB1RA_1LC0LF_0RA0LD_0LB1LE_0RA---_1LB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB0RE_1RC0LB_1LD0RD_1RA1LB_---0RF_0RB1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA1RF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB0LE_1RC0RB_1LD0RA_0LA0LC_1LA0LF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB0RA_1LC0RE_0LD0LB_1RE1LF_1RA0LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD0LC_1RE0LA_0RA0RF_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB0LE_1RC1LF_1RD---_1LA1RF_0LF1LE_0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB0LD_1LC0RC_1RA1LA_1LE1LF_---1RC_0RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB0RA_0LC0RF_1RC1LD_0LE0RA_1LB---_1LC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB1LF_1LB0RC_0RB0LD_1LE---_1LF0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB0LD_1RC0LF_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB1RF_0RC1RF_1LD0RA_0LE0RE_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB0RA_0LC0RF_1RC1LD_0LE0RA_1LB---_0RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB0LB_1RC0LE_1RD0RA_1LB0LF_---1LF_0RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB1LC_1RC0RF_1RD0LC_1LE0RA_0RC1LC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB0RB_0RC0RD_1LC0LD_1RE0LF_1RA---_1RC1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB0LD_1RC0LC_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD0RE_1LE0RA_0LA0LE_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB1RF_0RC1RE_1LD0RA_0LE0RE_1RA0LC_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB0LC_1LA0RD_1LB0LF_0RE0RA_1LB0RC_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB1LF_1LC0RA_1LA1LD_0LE0LB_0LC1LE_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1RB_1RA0LF_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LC_1RE0LA_0RA1RF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB0RD_0LC1RE_1LF1LD_1RA0LB_1LD0RE_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD0RA_0LE0RE_1RA0LC_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0RF_1RC1LF_0LC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB0LF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB0RA_0LC0RC_1LE1LD_0LB0LC_1RA1LF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB1RE_1LC0RA_0LD0LB_1RD1LA_0LE0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

