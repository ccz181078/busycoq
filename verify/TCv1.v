Require Import List.
From BusyCoq Require Import Individual62.
Require Import NArith.
From BusyCoq Require Import TC62.

Definition TC_param := [(rev (fst (Nat.iter 60 (fun '(x,y) => (y::x,(y*2)%N)) ([],1%N))),O)].

Ltac solve_TC :=
  apply (decide_TC_spec _ TC_param);
  native_cast_no_check (eq_refl true).


Lemma tm1: ~halts (TM_from_str "1RB1RD_1LC0LB_0RE0RA_1LD0LE_0LF1RC_1LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RC_1LC0RF_0LD0LC_1RE0LA_0RA---_0RC1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0LE_0RC1RC_0RD1RE_1LD0LA_1LF1RD_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1RF_1LC1RE_0LD1LD_1RE0LC_0RA1RD_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LF_0LB0LE_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB0RF_1LC0RA_0RD0LB_1RD0LE_0LD1RA_1RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0RE_1RC0RF_1RD0LC_1LE1RB_---1LC_0RA1RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0RA_0LC0LE_1LD0LC_1RA1LB_---1LF_1LF1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0RF_0RC0LE_1RD0LD_1LE0RA_1LC0LE_0RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB1RF_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RB_1RE0LD_0RB1LA_---1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0LC_1RC1RD_1LA1RC_1RE1LD_---0RF_0LF0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA1LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RA_1LA0LA_1RB1RF_1RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0RF_1RC0LE_0LD0RC_1RF1RE_1LB0LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD0LF_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB---_1LC0LF_1RA0LD_1LE1RF_0LC0LB_0RD0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB0LF_0LC0RC_1RB1RD_1RE---_1LF0RA_1LA0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB0LD_0LC1RE_1RA1LC_1LF1LA_0RB1RD_---0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA0RB_0RB0LE_1RD---_0LB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0RD_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0LD_1RC0RE_1LC1RD_0LE1LA_0LA0RF_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB0LA_1LC1RE_1LA0LD_1LB0RD_---1RF_1RA1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB1RE_1LC0RF_0LB0LD_1RE1LD_1RC0LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC1RF_0LD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0RB_1LC0LD_0LA1LA_1LC0RE_1RF1RA_---0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB---_1LC1RD_0LD0LB_0LE0RF_1RA0RA_0RC1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB0LA_1RC1LE_1RD0RA_1LB0RD_---1LF_1LD1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB0RB_1LC0RA_0RD1LD_0RE1LF_1RA0LB_1LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE1LD_0RE1LF_1RA0LB_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB1LD_1LC1RE_1LA1RC_0LC0LA_1RF1RB_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0RC_1RC1RF_1LD1LF_0RB0LE_---0LF_1RA0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB0LA_0LC0RD_1LA1LC_0RE1RD_1RA0RF_---1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB0RF_1RC0LE_1RD0RB_1LE1RA_0LA1LB_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE1LB_1RA0LF_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0LA_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB1RF_1RC0RA_1LD0RE_1LE0LE_1RB0LD_1RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB0RD_0LC0RE_1RA1LD_1LB1LD_---0RF_0LB1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD0RD_1LA0LA_0LF1LD_---1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB0RA_1LC1RE_0LD0LC_0RE0RF_0RA---_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1RA_1LC1RE_0LD0LC_0RE0RF_0RA---_1RF1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB0RC_1LC0RA_0RD0LC_1LE1LA_0LF---_1LB0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB1RF_0RC---_1RD0RB_1RE0LF_0LA0RE_1LD0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0LF_0RC0RB_1RD1RC_0LE0RA_0LA1LD_0LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0RC_1LC0RF_0LD0LC_1RE0LA_0RA---_1LE1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB0RD_0RC---_1RD0RA_1RE1LF_1LF0LE_0LA1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB0RE_1LC0RD_0LF1LA_1RA1RD_1LA0LB_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB---_1RC0RB_0LD0RF_0LE1LE_1LB0LC_1LC1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB1RD_1LC0RE_1LA1LD_0LC0LE_1LF0RA_0LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1LD_1RC1RE_1LA1RC_0LC0LA_1RF1RB_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB0LE_0RC---_1RD0LA_1RE1RF_1LC1LF_0RD0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB0LB_1LC1RE_0LD0LC_0RE0RF_0RA---_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB1RE_1LC0RA_0LF0LD_1LE---_0LB0LE_1LA0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB---_0RC1RE_1LD0LA_1LE0RF_0LF0LD_1RB0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB1LE_0RC0RF_0LD1LE_1RE0RA_1LA0LC_---0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RC0RB_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE1LD_0RE0LF_1RA0LB_0RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RF_1RC0LD_0RD0RB_1LE0RA_0LA1LC_1LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0RB_1RC1RB_0LD1RA_1LA1LE_0LF1LC_---0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1LD_1RC0LF_1LA0RA_0RC0LE_1LA0LA_---1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RA_1LA0LA_1RB0RF_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0RF_1RC0RA_1LD0RE_1LE0LE_1RB0LD_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB0RA_0LC0LE_0RD1LB_1RA---_1LA1LF_1RF0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RA_1LA0LA_1RB0RF_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB0RB_1LC0RA_0RD0LD_1LC1LE_1LF---_1RA0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB0RD_1LC0RE_0LD1LB_1RA0LE_0LA1LF_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA1LF_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB---_0RC0RB_1RD0LE_1LC0RF_1LD1LC_0RC1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB0LC_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB0LA_0LC1LD_1LA1LC_1RA1RE_---0RF_0RD1RF") c0.
Proof. solve_TC. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB0LD_1RC0LA_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB1RF_1RC0LC_0LD0RA_1LB1LE_0LA1LF_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB---_0RC1RD_0LC0LD_1RA1RE_1LC0RF_0RE1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA0LF_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA0RB_0RB1LE_1RC---_0LB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA---_1LA0LA_1RB0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB0LA_0LC0RD_1LA1LC_0RE1RD_1RA0RF_---0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB0RE_1LC1RD_1RA0LD_0LE1LC_0LC0RF_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE1LC_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB0RC_1LC0RF_0LD0LC_1RE0LA_0RA---_1LF1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB0RB_1LC1RE_0LD0LC_0RE0RF_0RA---_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0LD_1RC0LA_1LA1RF_0LA1RE_1LB---_0RA0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB0RD_1RC0RD_1LD0RA_1LB1LE_0LC0LF_1LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0RB_1LF0LE_0RA---_0LC0LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB0RF_0RC1LD_0LD0LF_1LE1LF_---1LB_1RA1RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RE_0LE---_1LA0LB_1RD1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB---_0RC1RE_1LD0RA_0LE0LD_1LB0RF_1RF1RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB0LE_0RC0RA_0RD1RA_1LE0RF_1LA0LD_0LD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB1LF_0RD1RF_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB---_1LC0RD_1LD0LD_1RE0LC_1RB0RF_1RE1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB0LD_1RC0LB_1LA1RF_0LA0RE_1LD---_0RA0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0LA_0RC1LE_1RD1RE_1LA0RC_1RC0LF_---1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB1RE_1LC0RC_0RA0LD_1LB0LD_0RD0RF_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0LE_1LC0RD_0RE1LD_1LB1LA_0LF0RB_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0RF_1RC0LD_0RD0RB_1LE0RA_0LA1LC_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB1RA_0LC0RD_0LD1LB_1RE0LF_0RA0RE_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB1RF_1LC0LE_0LD1LD_1RE0LC_0RA1RD_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB0RF_1LC1LE_1RD0LB_---1RA_0LA0RE_1RA0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB0LD_0LC1RC_1RA0RD_0LE0RC_1LA0LF_---1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB0LC_1LA1RD_1RC0LD_1LE0RB_---1LF_1LA0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB0LC_1LC1RF_1RA0LD_0LC1RE_1LA---_0RC0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1RC_0RC---_1LD0RA_0LE1LF_1RC0LD_0LA1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1LD_0LC0RD_---1LA_1LE0LB_1RF1RA_1RA0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB1LF_1RC0LF_1RD0RB_1LE0LC_0LA1LD_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE0LD_1LC0LF_1RA0LB_0RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB0RF_1RC0RA_1LD0RE_1LE0LE_1RB0LD_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB0LE_1RC0LD_1LB0RE_0LA0LC_1RB0RF_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB0RB_0LC0RA_1LE0RD_1LB---_0LF0LA_1LA1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB0RE_0RC1RA_1LD1RF_1LE0RF_1LA0LD_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB0RA_1RC0LC_0LD0RA_1LB1LE_0LA0LF_1RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB---_1RC0RA_1RD0LE_1LC0RB_0LF0LD_1RC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE1LD_0RE0LF_1RA0LB_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB1RF_1LC1LF_1RA0LD_1RE0LB_0RC---_0RA0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB0LE_0RC1RD_1LA0RB_0RE1RA_1LF1LA_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB0RB_1LC0RC_1RE0LD_0LE0LC_1RA1LF_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB0RF_0RC0LA_1RD0LE_1RE1LB_1LD1RA_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB0RC_1LC0LF_1RE1LD_0LB0RA_---0RB_1RF0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB1LC_1LA0RF_1RD0LA_---1RE_1RB0RB_1LF0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LD0LF_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB---_1LC0RE_1RE1LD_0LE0LF_1LB0RF_0RE1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB1RD_1LC1LD_1LF0RA_1LE1RC_---0LB_1LA1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB0RF_1LC1LE_---0LD_1LA0LB_0LA1RF_1LF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB0LC_1RC0RD_1LA1LC_1RF0RE_1LE1RC_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB0LF_0LC1LA_1RE0LD_1LB---_0RA0RE_1LF1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB1LD_1RC1RE_1LA0LE_0LC0LA_1RF1RB_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB---_1LC0RC_0LD1LD_1RE0LC_0RF1RD_1RB1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB---_0RC0LF_1RD0LA_0RE0RF_1RF1RC_1LB0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB1LD_0RC0RB_0LD0LF_0LE---_1LA0LE_1LF1LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA0RF_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB0RA_0RC1RF_1LD0LF_0LE---_1LF0LC_1LA1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RA0RB_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB0LB_1RC0LC_1LD1RE_---0LE_0RA0LF_1LB1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB1LD_1RC1LB_1LA1RE_1LF1LA_0RB0RC_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RE_0LA0LF_1RC0RC_1LD0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB1RA_0LC1RD_0LD1LC_1RE0RB_0RA0RF_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB---_1LC1RE_0LD1LD_1RE0LC_0RF1RD_1RB1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA1RC_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB1RA_1LC1RE_0LD0LC_0RE0RF_0RA---_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB0LA_0RC1RF_0LD1RD_1LE0RB_---1LF_1LA0RF") c0.
Proof. solve_TC. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RE_0LE---_1LA0LB_0LB1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB0RB_1LC0RF_1RB1LD_1RE0LC_---1RA_1LF0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB0RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB1RA_0RC0LF_1LC0LD_1RE1LF_0RA---_1LD1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB0RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB0RB_1LC0RA_0LE0LD_1LC0LF_1RF1LB_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB1RE_1LC1RF_1RD1LC_---0RA_1RA0LF_0RC1LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB0LF_0RC0RD_1RD1RA_1LE0LE_0RA0LD_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RE_0LE---_1LA0LB_1RF1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB0RD_0RC0RA_1LD1RE_0LE---_1RB0LF_1LE0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB0RB_1RC---_1LD1RE_0LE0LC_0LA0RF_0RD1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB0RE_1LC0RD_1LF1LA_1RA1RD_1LA0LB_---1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB0LC_1LC1RD_1RF1LD_1RE1LA_---0RC_1RA0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB0LD_1RC1RE_0LD0RF_1LE1LD_1LA1LC_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB0LE_0RC1RD_1LD0RB_0RE1RA_1LF1LA_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB0RE_1LC1RA_1RB0LD_1LC1RB_0RF0RD_---0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA0RF_0LD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB0LA_1LC1RD_1RC0LD_0LC0RE_1RF---_1RA0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB0LC_0RC1RE_1LD0LF_1LE0RA_0LA0LD_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE0LD_1LC1LF_1RA0LB_1LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB1RC_0LA0RA_1RD---_1LE0RF_1LF0LF_1RB0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA0RC_0RB0LE_1RD---_0LB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB1RD_1LC1RB_1RA0LB_1RE1LD_---0RF_0LF0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB0LF_1RC0RA_1LD0LB_0LE1LC_1RA1LF_0LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB---_1LC0LE_0LD1LD_1RE0LC_0RF1RD_1RB1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LB_0LE0LB_1RA0LF_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB0LD_1RC0RB_1RD1RE_0LE0RF_1LA0LE_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB1RA_1LC0RB_0RA1RD_1LB1LE_---0LF_0LD1LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB1LD_1RC0RF_1LA0RC_---1LE_1LC1LF_1RA0LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE1LD_0RE1LF_1RA0LB_1LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB0LB_0LC0LF_1LB0RD_0RE---_1RC1RA_1RA1LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm177: ~halts (TM_from_str "1RB1RA_1LC0RB_0RA0LD_0LE1LD_1LB1LF_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm178: ~halts (TM_from_str "1RB0LC_0RC1RE_1LD0LF_1LE0RA_0LA0LD_0RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm179: ~halts (TM_from_str "1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LC_---1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm180: ~halts (TM_from_str "1RB0LC_1LA0RD_1LB0LF_0RE0RA_1LB0RC_1LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm181: ~halts (TM_from_str "1RB1LC_1RC0RB_0LD0LE_1LA0LD_---1LF_1LF1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm182: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD0LB_1RA0LE_1RA0RF_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm183: ~halts (TM_from_str "1RB0RF_1RC0LD_1LB0RA_0LE0LC_1RB0LA_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm184: ~halts (TM_from_str "1RB0LA_1RC0RC_1LD1RB_0LF1LE_---1LA_1LE0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm185: ~halts (TM_from_str "1RB0RB_1LC0RA_1LE0LD_1LC0LF_1RA0LB_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm186: ~halts (TM_from_str "1RB0RA_1LC1RD_1LD0LC_0RA0RE_---1RF_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm187: ~halts (TM_from_str "1RB---_1LC0RD_1LD0LD_1RE0LC_0LF0RF_1RE1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm188: ~halts (TM_from_str "1RB1LF_1RC0RC_1LD0RD_1RA0LE_0LA0LD_---0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm189: ~halts (TM_from_str "1RB1RF_1LC0RC_0LD1LD_1RE0LC_0RA1RD_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm190: ~halts (TM_from_str "1RB0LD_1RC0RC_0LA1RE_---1LC_1RB1RF_1LA0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm191: ~halts (TM_from_str "1RB0LC_1LA1RD_1LA1RB_1RB0RE_0RF0RC_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm192: ~halts (TM_from_str "1RB1RC_0RC---_1LD0RA_0LE1LF_1RF0LD_0LA1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm193: ~halts (TM_from_str "1RB1RE_1LC0RA_1RD0LC_0RA1LE_1RA0LF_---1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm194: ~halts (TM_from_str "1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC0RF_0LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm195: ~halts (TM_from_str "1RB0RE_1RC1RE_0LD0RF_1LE1LD_1LA1LC_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm196: ~halts (TM_from_str "1RB0RF_1LC1LE_1LE0RD_1RA1RC_1LD0LB_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm197: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_0RE0LE_1LD1LF_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm198: ~halts (TM_from_str "1RB0RE_1RC1LD_1LD0LC_0LE1LB_1RF0RB_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm199: ~halts (TM_from_str "1RB0RB_1LC0RD_0LD1LC_0LE0LF_0RF---_1RA0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm200: ~halts (TM_from_str "1RB0LC_0RC1RB_0RD0RE_0LE---_1LF0RF_1LA0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm201: ~halts (TM_from_str "1RB0LA_1RC---_1RD0LE_1LE1RE_1RF0LF_1LA0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm202: ~halts (TM_from_str "1RB0LB_1LC1LB_0RD1LA_1LA1RE_0RF1RC_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm203: ~halts (TM_from_str "1RB0LF_1RC0RC_1RD1RC_0LE1RB_---1LF_0LA1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm204: ~halts (TM_from_str "1RB0RF_1RC0LB_1LD0RE_1RE1LB_1RA0RD_---1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm205: ~halts (TM_from_str "1RB---_1RC1LF_0RD0RB_1LE0RE_1RD0LF_0RA0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm206: ~halts (TM_from_str "1RB1LA_1RC0RD_1LD1LE_0RA0LC_1RE0LF_---1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm207: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_0RD1LE_1LC0LA_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm208: ~halts (TM_from_str "1RB0RC_1LC1LE_0RD0LB_1RA1LD_1RE0LF_---1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm209: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0RC_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm210: ~halts (TM_from_str "1RB---_1RC1RF_0LD0RC_0LE1LD_1RA0LB_0RB1RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm211: ~halts (TM_from_str "1RB0RE_1RC0RF_1RD0LC_1LE0RA_1RA1LC_---1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm212: ~halts (TM_from_str "1RB0LE_0RC0RA_1LD1LA_1LE0LF_1LA1LC_0LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm213: ~halts (TM_from_str "1RB0RE_0LB1RC_1LD0RA_1RA1LE_1RF0LD_---1LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm214: ~halts (TM_from_str "1RB0RE_0RC1RE_1LD1RF_1LE0LD_1RA0LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm215: ~halts (TM_from_str "1RB0LD_0RC0RE_1RD0LE_1LA0LD_1RF---_0RA0RF") c0.
Proof. solve_TC. Time Qed.

Lemma tm216: ~halts (TM_from_str "1RB1RE_1LC0RF_1RD1LB_---1RA_1LF0LD_1RD0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm217: ~halts (TM_from_str "1RB0RC_1LA0RE_1LB1LD_0LC0LF_0RA1RA_1LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm218: ~halts (TM_from_str "1RB1LA_0LB1RC_0LA1RD_1RA0RE_0RF0LF_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm219: ~halts (TM_from_str "1RB0LD_1RC0RE_1LD0RC_1LA0LC_1RF0LA_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm220: ~halts (TM_from_str "1RB0LC_0LB0RC_1LD0LF_1LE---_1LA0LA_0RF0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm221: ~halts (TM_from_str "1RB0RD_0LC0RC_1LD1LB_1RE1LF_---0RA_0RB1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm222: ~halts (TM_from_str "1RB1RA_1LC0RF_---0LD_0LE1LB_1RE0LF_0RA1RF") c0.
Proof. solve_TC. Time Qed.

Lemma tm223: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RD_1RC1RA_---0LF_1LD0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm224: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA0LF_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm225: ~halts (TM_from_str "1RB0LC_1RC0RA_0RD1LD_0LE1LA_1LA0LF_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm226: ~halts (TM_from_str "1RB0RB_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm227: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1LC0LA_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm228: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm229: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LE_0LB0LF_0LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm230: ~halts (TM_from_str "1RB0LF_1LC0LB_0RD1RC_1LE0RE_0LA1RB_---1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm231: ~halts (TM_from_str "1RB1LF_0RC0RE_1LD0RA_1LE---_1RC0RF_0LA0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm232: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RD_1RC0LE_0RF0LC_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm233: ~halts (TM_from_str "1RB0LB_1LC1LE_---1LD_1LA0LA_1RF1RA_1LF0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm234: ~halts (TM_from_str "1RB0RD_1LC1RF_1RA1LD_0RE0LC_---0LC_1LC0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm235: ~halts (TM_from_str "1RB1LE_1RC1RB_0LD0RF_0RB1LA_0LA1LC_---1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm236: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_0LB0RB_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB0RD_1LC1RF_1RA1LD_1RE0LC_---1RB_1LC0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm238: ~halts (TM_from_str "1RB1LF_1RC0RB_1LD0RA_1LE0LC_0LA1LC_0LD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm239: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm240: ~halts (TM_from_str "1RB1RD_0LC1LB_0LF1LD_0LE0RD_1LB---_1RF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm241: ~halts (TM_from_str "1RB0LD_1RC0RB_1RD0RE_0LC0LE_1LF0RD_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm242: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LA_0RA1LE_0LF---_0LA0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm243: ~halts (TM_from_str "1RB1LC_1LC0RC_1LD0RB_1LA1LE_0LF---_0LD0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm244: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LE_0LB1LF_0RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm245: ~halts (TM_from_str "1RB1LF_1LC0RD_1LA0LB_0RB0LE_1RD---_0LB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm246: ~halts (TM_from_str "1RB0LE_1RC0LE_1RD0LB_1LB1RF_1RC1LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm247: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_0RA0LA_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm248: ~halts (TM_from_str "1RB0LF_0RC0RD_1LD0RD_1LE0RA_1RD1LF_1LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm249: ~halts (TM_from_str "1RB0RB_0RC1RF_1RD0LE_1RE0RA_1LC0LE_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm250: ~halts (TM_from_str "1RB1RE_1LC1LF_1LD1LB_1RE0LE_1LD0RA_---1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm251: ~halts (TM_from_str "1RB0RD_1LC1RF_1RA1LD_1RE0LC_---1RB_0LE0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm252: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_1LD0LA_---0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm253: ~halts (TM_from_str "1RB0LB_1LC1LB_0RD1LA_0LB1RE_0RF1RC_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm254: ~halts (TM_from_str "1RB0LE_0LC0RE_0RA1LD_1RA1LF_---1RD_0LD1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm255: ~halts (TM_from_str "1RB1LD_1LC0RE_1LA0RA_0LB0LE_0RB0LF_1RE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm256: ~halts (TM_from_str "1RB0LB_1LC1RD_1RF0LD_1LE0RC_1LA1LD_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm257: ~halts (TM_from_str "1RB1RD_1LC0LC_0RD0LB_1RF0LE_1RC---_0RA0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm258: ~halts (TM_from_str "1RB---_0RC0RB_1LC0LD_1LA1LE_1LD0RF_1LA1RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm259: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LC_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm260: ~halts (TM_from_str "1RB0LE_1RC0RE_0LD0RF_0LA1LA_1RA1LD_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm261: ~halts (TM_from_str "1RB0RE_0LB1RC_1LD0RA_1RA1LE_0RF0LD_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm262: ~halts (TM_from_str "1RB0LC_1LC0RB_0RE1LD_1LA0LD_0RF1RA_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm263: ~halts (TM_from_str "1RB0RB_1LC0RD_0RC0LD_1RE0RF_1RA---_0LF0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm264: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_0LD1RE_1RA0RB_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm265: ~halts (TM_from_str "1RB---_0RC1RB_0RD1RF_1LD1LE_1LB1LF_0RA0LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm266: ~halts (TM_from_str "1RB0RE_1RC1LB_0LC1RD_0LB1RA_0RF0LF_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm267: ~halts (TM_from_str "1RB0LF_1LC0RC_1RD1RC_0LE1RB_---1LF_0LA1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm268: ~halts (TM_from_str "1RB0RD_1LC1RF_1RA1LD_1RE0LC_---1LA_0LE0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm269: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0LD_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm270: ~halts (TM_from_str "1RB0LB_1RC0LA_1RD1RE_1LA1RB_0RF---_0RC0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm271: ~halts (TM_from_str "1RB1RA_1LC0LF_1RA1LD_1LB1LE_1LB0LC_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm272: ~halts (TM_from_str "1RB0LF_0RC1RD_1LC1RB_1LE1RC_---0LA_1LB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm273: ~halts (TM_from_str "1RB1RE_1LC0RF_1RA0LD_1LB1LD_---0RD_0RA1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm274: ~halts (TM_from_str "1RB0RE_1RC1LB_0LC1RD_0LB1RA_0RF0LC_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm275: ~halts (TM_from_str "1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RB0RC_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm276: ~halts (TM_from_str "1RB1LA_0LB1RC_0LA1RD_1RA0RE_0RF0LC_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm277: ~halts (TM_from_str "1RB1LF_0RC0LB_1RD0LA_0RE0RD_1LE1LC_---0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm278: ~halts (TM_from_str "1RB0RD_1LC1RF_1RA1LD_1RE0LC_---1LA_1LC0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm279: ~halts (TM_from_str "1RB1RF_1LC0LF_1LE1LD_1LC---_1RF0LF_1LE0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm280: ~halts (TM_from_str "1RB1RF_1LC0RA_---0LD_1LE0LF_1RB0LE_1LA0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm281: ~halts (TM_from_str "1RB0RD_0LC1LD_1RC1LB_1RE1LC_---0RF_1RD0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm282: ~halts (TM_from_str "1RB0LE_1RC0LE_1RD0LB_1LA1RF_1RC1LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm283: ~halts (TM_from_str "1RB0LB_1RC0LD_1LB1RE_1LF0RE_1RA---_0LA0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm284: ~halts (TM_from_str "1RB0LB_0RC1LD_1LD0RF_1RE0RD_0LA1LE_---1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm285: ~halts (TM_from_str "1RB0RC_1LC1RD_1RD1LB_0RA0LE_---1LF_0LD0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm286: ~halts (TM_from_str "1RB1RD_1LC0RC_1RE1LD_1RA0LE_1LF0RD_---0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm287: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LA_0RA1LE_0LF---_0LA0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm288: ~halts (TM_from_str "1RB1RA_1LC0RB_0RA0LD_0LE1LD_1LB0LF_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm289: ~halts (TM_from_str "1RB1RA_0LC0RF_0RA1LD_1RA1LE_0LD1LB_---1RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm290: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm291: ~halts (TM_from_str "1RB---_0RC0RA_1LD0RE_1RC0LF_1RC1RA_1LD0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm292: ~halts (TM_from_str "1RB0RD_0RC0RF_1RD1RC_0LE1RA_0LA1LE_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm293: ~halts (TM_from_str "1RB1RF_1LC0LE_1LD1LB_1RE0LF_---0RA_1LD0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm294: ~halts (TM_from_str "1RB0RE_0LB1RC_1LD0RA_1RA1LE_1RF0LD_---1RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm295: ~halts (TM_from_str "1RB1LE_1RC0LF_0LD0RF_0RB1LA_0LA1LC_---1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm296: ~halts (TM_from_str "1RB0LE_1LC0LB_1RD0LB_0RA0RE_1RF---_0RC0RF") c0.
Proof. solve_TC. Time Qed.

Lemma tm297: ~halts (TM_from_str "1RB0RF_1RC---_1RD0RD_1LE0RA_0RE0LA_0LF0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm298: ~halts (TM_from_str "1RB1RE_1RC0RF_1LD1RA_1LB1LD_0LC0RC_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm299: ~halts (TM_from_str "1RB1LE_1RC0LA_1RD0RA_0LE0RF_0LB1LB_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm300: ~halts (TM_from_str "1RB1RA_1LC0LF_1RA1LD_0RD1LE_1LB0LC_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm301: ~halts (TM_from_str "1RB1RA_1LC0LF_1RA1LD_1LB1LE_0RC0LC_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm302: ~halts (TM_from_str "1RB---_0RC0LA_1LD0RB_1LE0RE_1RC1LF_0LC0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm303: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD0LB_1LE0LF_1LA0RE_---1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm304: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_0RE1LE_0RA1LF_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm305: ~halts (TM_from_str "1RB0LD_1RC1RE_1LD1RA_1RA0LA_0RF---_0RB0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm306: ~halts (TM_from_str "1RB0LB_1RC0LE_1RD0LB_1LB1RF_1RC1LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm307: ~halts (TM_from_str "1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA1LF_1LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm308: ~halts (TM_from_str "1RB1LE_1LC0RE_---0LD_1LA0RA_1RF0LB_1RD1RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm309: ~halts (TM_from_str "1RB1RE_1LC1RD_1RD0LD_1RA0LC_0RF---_0RA0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm310: ~halts (TM_from_str "1RB0LB_0RC0RF_1LD0RE_0LA---_1LA0RD_0LE0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm311: ~halts (TM_from_str "1RB1RA_1LC0RB_0RA0LD_0LE1LD_1LB0LF_---0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm312: ~halts (TM_from_str "1RB1LA_0LB1RC_0LA1RD_1RA0RE_0RF0LB_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm313: ~halts (TM_from_str "1RB0RA_1LC0RE_1LD0LB_0LE1LB_1RA1LF_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm314: ~halts (TM_from_str "1RB0LD_1LC1RD_1LA1LC_1LF1RE_1RA0RB_---1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm315: ~halts (TM_from_str "1RB1LA_1RC0RF_1LD0RC_1LE0LD_0LA1LC_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm316: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD1RA_1LE1RF_1LA0LE_0RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm317: ~halts (TM_from_str "1RB1LD_1RC0RA_1RD0RF_1RE0LD_1LA0RB_---1LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm318: ~halts (TM_from_str "1RB0LA_1LC0RE_---0LD_1LA0LF_1RB1RF_1LE0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm319: ~halts (TM_from_str "1RB0RF_1LC1RD_1LA1LC_1RA1RE_1RA0RB_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm320: ~halts (TM_from_str "1RB0LA_1LC0RD_1RD1LA_1RE0RC_1RA0RF_---1LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm321: ~halts (TM_from_str "1RB1RE_1LC0RF_1RD1LB_---1RA_1LF1RB_1RD0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm322: ~halts (TM_from_str "1RB0RC_1RC0RF_1LD1RE_1LB1LD_0LE1RA_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm323: ~halts (TM_from_str "1RB0RA_0LC1LB_1RD0LD_0RE1LA_1LA0RF_---1RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm324: ~halts (TM_from_str "1RB1RE_1LC0LF_1LD1LB_1RE0LE_1LD0RA_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm325: ~halts (TM_from_str "1RB0RD_0LC1LD_1RC1LB_1RE1LC_---0RF_1LB0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm326: ~halts (TM_from_str "1RB0RC_1RC0RF_1LD1RE_1LB1LD_1RB1RA_---0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm327: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_1LE---") c0.
Proof. solve_TC. Time Qed.

Lemma tm328: ~halts (TM_from_str "1RB0RE_1RC1LB_0LC1RD_0LB1RA_0RF0LD_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm329: ~halts (TM_from_str "1RB0RA_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD") c0.
Proof. solve_TC. Time Qed.

Lemma tm330: ~halts (TM_from_str "1RB0RB_1LC1RB_0RF1LD_1LE0LC_1LA---_1RF0RC") c0.
Proof. solve_TC. Time Qed.

Lemma tm331: ~halts (TM_from_str "1RB---_1RC1RF_0RD1RA_0RE0RC_1LF1LB_0LE0LE") c0.
Proof. solve_TC. Time Qed.

Lemma tm332: ~halts (TM_from_str "1RB---_1RC0LE_0RD0RB_1RE1RF_1LB0LC_0LF1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm333: ~halts (TM_from_str "1RB1LE_1RC0LA_1LD0RB_1LE1LD_1LF0LB_0LA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm335: ~halts (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_0LD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm336: ~halts (TM_from_str "1RB0LB_1RC0LD_1LD0RE_1RA0LC_1RF---_1RA0RB") c0.
Proof. solve_TC. Time Qed.

Lemma tm337: ~halts (TM_from_str "1RB1RE_1LC0RF_1RA1LD_1RC0LD_0RC1RC_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm338: ~halts (TM_from_str "1RB1RE_1LC0RF_1RA0LD_1LB1LD_---0RD_0RA0LF") c0.
Proof. solve_TC. Time Qed.

Lemma tm340: ~halts (TM_from_str "1RB---_1RC1RF_0RD1RA_0RE0RC_1LF1LB_0LE0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm341: ~halts (TM_from_str "1RB---_0RC0RC_1RD0LF_1RE1RA_1LE0LC_1RD1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm342: ~halts (TM_from_str "1RB---_0RC0RA_1RD0LF_1RE0LE_1LC1RE_1RA0LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm343: ~halts (TM_from_str "1RB---_1RC0LE_0RD0RB_1RE1RF_1LB0LC_1RB1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm344: ~halts (TM_from_str "1RB1RF_1RC0LE_0RD0RB_1RE1RA_1LB0LC_1RB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm345: ~halts (TM_from_str "1RB0LC_1LC0RF_1LD0LB_1RE0LC_1RA0RD_0RC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm346: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LA_1RE1LE_0LF---_0LA0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm347: ~halts (TM_from_str "1RB---_0RC0RF_1RD0LF_1RE1RA_1LE0LC_1RD1LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm348: ~halts (TM_from_str "1RB1LD_1RC0RE_0LA1RB_0LF1LA_0RC1RE_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm349: ~halts (TM_from_str "1RB1LB_0LC---_0LD0RD_1RE0LE_1LF0RE_0LA1LD") c0.
Proof. solve_TC. Time Qed.

Lemma tm350: ~halts (TM_from_str "1RB0LC_1LA0LD_0LB1LB_1RA1RE_0RD0RF_1RD---") c0.
Proof. solve_TC. Time Qed.

Lemma tm351: ~halts (TM_from_str "1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LB0LC_---0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm352: ~halts (TM_from_str "1RB1LD_1RC1RE_1LA0RF_1RA0LD_0RA1RA_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm353: ~halts (TM_from_str "1RB1RA_1LC0RC_0RA0LD_0LB1LE_1LC0LF_0LC---") c0.
Proof. solve_TC. Time Qed.

Lemma tm354: ~halts (TM_from_str "1RB---_0LC0LE_1RC1LD_1RE1RF_1LB0RD_0LF0RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm356: ~halts (TM_from_str "1RB1LE_1LC0RD_0RD0LB_1LE1RC_1LA0LF_---0LC") c0.
Proof. solve_TC. Time Qed.

Lemma tm358: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD1RB_1RE0LA_0LA0RD_---0RE") c0.
Proof. solve_TC. Time Qed.

Lemma tm359: ~halts (TM_from_str "1RB1RF_1LC0RA_1RE1LD_0LB0LD_---0RC_1RA1RA") c0.
Proof. solve_TC. Time Qed.

Lemma tm360: ~halts (TM_from_str "1RB1RF_1LC0RA_1RE1LD_0LB0LD_---0RC_1RA0LA") c0.
Proof. solve_TC. Time Qed.

Lemma tm362: ~halts (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RB_1RF1LC_0RA---") c0.
Proof. solve_TC. Time Qed.

Lemma tm363: ~halts (TM_from_str "1RB1RF_1LC0RA_---0LD_0LE1LF_0RF0LB_1RA0LB") c0.
Proof. solve_TC. Time Qed.

Lemma tm364: ~halts (TM_from_str "1RB0LD_0RC0RA_1LC1RD_1LA1LE_0RE0LF_1LB---") c0.
Proof. solve_TC. Time Qed.

Lemma tm366: ~halts (TM_from_str "1RB1RC_1RC1RB_1LD0RA_---1LE_1LF0LA_0LA0LC") c0.
Proof. solve_TC. Time Qed.

