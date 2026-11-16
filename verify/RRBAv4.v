From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMAddOneSymbol.
Module BB62' := TMAddOneSymbolCtx BB62.
Module RRBA62 := RRBA BB62'.
Module BB62'spec := TMAddOneSymbol BB62.
Require Import NArith.
Require Import String.


Ltac solve_loop1''' min_b mid_d n_skip k T :=
  rewrite halts_halts';
  apply BB62'spec.from_nonhalt;
  rewrite <-RRBA62.TM.halts_halts';
  apply (RRBA62.decide_loop1_spec' _ (min_b,mid_d) n_skip k T);
  native_cast_no_check (eq_refl true).
Ltac solve_loop1'' min_b n_skip k T := solve_loop1''' min_b 8 n_skip k T.
Ltac solve_loop1' n_skip k T := solve_loop1'' 8 n_skip k T.
Ltac solve_loop1_0 T := solve_loop1' 1%nat O T.
Ltac solve_loop1 := solve_loop1_0 1000%N.

Close Scope sym.


Lemma tm1: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA1RE_1LB0RD_0RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1LE_0RC1RC_1LC0RD_---0LE_1LA1RF_1RC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1LD_1LC1LD_0RF0RA_0LE0LD_1RA1RF_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0LF_1LC0LB_---0RD_1LF1RE_1RD1LB_1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LD_1LB1RC_1RF1LD_0LE0RA_0RA0LD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB1LA_1LA0RC_1RB0RD_1LE1RD_0LC0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1LA_1RC0RD_0LC1RD_0LA0LE_0RB1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB1RA_1LC1LB_1LE0LD_1RE0LC_0RA0RF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0LA_1LC1RF_0RA1LE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB1RA_1RC0RB_1LD1RD_---0LE_0LA0LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB0LE_1LC---_0RD0LC_0RE1RF_1LC1LE_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1LD_0RC1RF_0LD---_1LE0RD_1LA0LB_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0LE_0RC---_1RD1RC_1LA1LF_0RB0LA_1LD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0LD_1RC0LA_1LB1RC_1RE1LD_1LF0RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB1RF_0LC0RB_0LA1LD_1LA1RE_---0RF_1LC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1RE_1LF1RD_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB1LF_1RC0LD_1RD0LB_0LE0RC_1RB0LA_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LD_0LC0RB_1LF1RD_1LE1LD_1LC1RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB1LD_0RC1LC_1RD1RC_1LE1LF_0RB0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB---_0RC1LD_1RD1RF_1LE1LB_0RA0LE_1RC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB1RA_1LC1LF_1RE0LD_0RE0LC_0RA---_0LE1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RE_0RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LB_1LA1RE_0RF0RE_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA0LD_0RE0LD_0RF---_0RB1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1RE_0RE0LD_0RF1RA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0LA_1LC0RB_1LF1LD_1LE---_1LA1RF_1RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB1LD_1RC0LB_1LA1RB_0RE0LD_1RF---_0RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB1LD_1RC---_1LD1RA_0RD0LE_0RB0LF_0LD0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB---_1RC0LB_1RD1RE_1LE1RA_0RB1LF_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB1LE_1LC1RC_0RD0LC_0RE---_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB---_1LC1LB_1LF0RD_1RE1RD_1RC1LB_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB0RC_1LA---_1LE1RD_1RC1LE_1RA0LF_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LF_1RD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0RB_1RC1LB_1RD1RA_1LE0RF_0RA0LE_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB0LE_0RC---_1RD1RC_1LA1LF_0RB0LA_1LD0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB---_0RC1RE_1LD0LD_0RB0LC_1RF0RE_1LD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE0LF_1LC1RE_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB0LF_1RC1RA_0RD1RE_1RE---_1LF0RB_0RD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_0LF0LC_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB1LE_1RC---_0RD1LD_1RE1RD_1LF1LA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB1LF_1LC0LE_0RD0LC_0RB1RA_1RD---_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB1RD_1LB1LC_1LD1LF_0RA0RE_0LF1RA_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB---_1LC1LB_1LE1LD_0RE0LD_0RF1RF_1RA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB0RE_1RC---_1LD1LC_1LF1LA_1RD1RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LC_0LA1LF_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB0LD_0RC1LD_1LA1RE_---0RC_1RC1LF_0LB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0RB_0RC1RC_1LD0LA_0LE0RC_---0LF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB1LF_1LC0LF_---0RD_1LF1RE_1RD0LC_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB0LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1RE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB1LE_1LC1RA_0RB1LD_1RC0LD_1LF0LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB---_0RC0LF_0RD0RC_1LD0LE_1RC1LB_0LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA0RE_0RD0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB0LA_0LC0RB_1LA1LD_1LE1LC_1RF1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1RA_1RC1RE_1LD0RA_---1LB_0LF0LD_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB1LF_1LC0RD_0RB0LC_1RA1LE_1RD1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB---_1LC1RF_0RA0LD_0RE0LE_0LC0RE_1RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB1LB_0RC0LF_1RD---_1RE0LD_1LA1RD_0RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB1LE_1LC0RB_1RD0LC_0RA1RA_0LF0LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1LA_1LC1LE_0RD0LC_0RE1RF_1RA1RD_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RC_0RC0LC_1LD0RE_0LA0LD_1RF1RC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB1RF_1LC1LB_0RF0LD_0RE0LC_0RB---_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1RE_0RC0LD_1LD1LC_0RA0LB_1RC1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA---_0LA1RF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0LD_1RC1LF_0LA1RA_---1LE_0LF1LA_0RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB1RC_0RC---_1RD0RD_1RE1LD_1LF1RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB0LB_1RC0RE_1LD1LC_1LA0LD_0RF---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB1LF_1LC0RD_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB1LE_0LC0RB_0LE1LD_1LC---_1LA1RF_0RC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB0LC_0LC0RE_1RD1LC_1LC0RB_1LF1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0LC_1LC0RD_1RB1LC_---0RE_1LF1RE_1LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB0LC_1LC0RD_1RB1LC_---0RE_1LF1RE_0LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD1RE_0RC0LD_1LB---_1RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB0RA_0LB0LC_1LD1LE_1RA1RD_0RA0LF_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE1RA_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA1RB_0RF0LB_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LD_1LD1RA_0LE0LF_0RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB1RE_1LC---_0RA0LD_0RB0LC_1RF0RF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LC_1RC1RE_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE1LA_1LA0RB_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB1LA_0RC0LD_1LD1RF_1LE0RB_---0LA_0LE1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RF1LB_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB1LD_0RE0RB_---1RD_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB1RC_0RC---_1LD1RA_0LE1RF_0RA0LE_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB0LD_0RC0RE_1LC0LA_0RA1LD_---1RF_1LC1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0LD_1RC0LA_1LB1RC_1RE1LD_1RB0RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB1RA_1RC0RB_0RD---_1LD1RE_0LF0LE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB1LA_1LA1RC_1LD0RC_0LE---_0LF1RB_1LF0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB1RD_0LC0LA_1LC1LA_0RE0RF_0LC0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB1RC_0RC---_1RD0RD_1RE1LD_1LF1RA_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB1LD_1RC---_1LC1RA_0LE0RA_---0LF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LB_1LA1RD_1LD1LF_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LF0LD_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB1RF_1RC1LE_1LD1LE_0RF0RB_0LA0LE_0RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB1LC_1LB1RA_0LF0LD_1RE0LC_0RA---_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB1RE_1RC---_1LD0RA_0RB0LD_1LF1RA_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB0RB_1LC1RB_---0LD_0RE0LF_1LA0RA_1RE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0LA_0RC1RC_1RD1LA_1LE1LA_---0LF_0RB0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LC_0LE1LE_1LA---_1RC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB1LF_1LC0RB_1LD0LB_1RE0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD0RE_0RC0LD_1LF1LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB0LE_0RC1LF_1RD1RC_1LA1LD_0RB0LE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB1LD_1LC1RA_1RF1RA_0LF0LE_0RB0LD_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB0LF_1RC1RA_0RD0RB_1LD0LE_0RB0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB1RC_0RC---_1LD1RA_0LE0LF_0RA0LE_1RF1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA0RE_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1LF_0RC1LB_1RD1RC_1RE---_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB1RF_1LC1LB_0RD0LC_1RE1RA_0RB1RD_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB1RA_1LC1LB_1LD0LC_1RE0LF_0RA0RE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB0RA_0LB0LC_0LD1LE_1RE---_1RF1LB_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB1RD_1RC1RF_1LD0RA_1RA0LE_0RB1LD_1LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB1RA_0LC1LD_1LA1LC_---1LE_1RF0LB_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB1RF_0LC0RB_0LD1LB_1LE---_1LA1LE_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB0LB_0RC0LB_0RD---_1RE0LA_1RF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE---_1RA1RE_1RD1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LF1LE_0RB1LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB1RD_0LC0LA_1LA1LC_0RE0RF_0LA0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_0LB---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_0LE0LF_0LC0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB1RC_0LC1RE_0RE0LD_1LA0LF_0RA1LC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB1LD_1RC0LF_1LC1RA_0LB0LE_---1RF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RE---_1RF0RF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD0LD_1RA1LE_1LD0RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB0LD_0RC0RE_1LC0LA_0RA1LD_0LF1RE_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB1LB_0RC0LB_1LB0RD_1RE0LD_1RF---_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB0LE_0RC1RB_1LC1RD_0LA1RD_---1LF_0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB0RB_0LC0RD_---1LA_1RE1LF_1LC1RD_0LB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RE_1RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB---_1RC1LE_1LD0RB_0RC0LD_1RF1LB_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB1RF_1RC0RF_1LD1LC_1RA1LE_0RB0LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB0LB_1LC0LF_---0RD_1LA1RE_1RD1LA_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB0RC_0LC0LE_1RC0RD_1LB1RD_---0LF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RE_0RA0LD_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB1LB_1LC1RF_0RE0LD_0LC0RD_1RA---_1RE1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB1RA_1LC1LF_0RD0LC_0RE---_1RA1RD_1LE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB0LA_1RC---_0RD1RD_1RE1LA_1LF1LC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB1RA_0RC0RB_1LD0LC_0LE---_1LF1LC_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_1RE0LF_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB1RF_1LC1LB_1LD0LC_0RE0RA_---0RA_0LC1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB---_1RC1LB_1RD1RF_1LE0RA_0RC0LE_1RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0LA1LD_0RF0RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB1RA_1LC1LB_1LF1RD_0RC1LE_0RD0LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB---_1RC1LC_1LC1RD_1RA1LE_0RA0LF_0LE0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB1RC_0RC---_1RD1RE_1RE1LD_1LF1RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB0LE_1RC0RF_1RD1LA_1LE0RB_0LF1LB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB---_0RC1RC_1RD1LE_1LB1LF_1RA0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE1LA_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB1LC_1LC1RA_0LE0LD_1RE0LC_1LF0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB1RD_1LC0RE_0LC1RA_0RB0RD_0RF---_1LF1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB1RD_1LC0LB_---0RA_1RE1LB_1LF1RD_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB1LE_1RC0RF_1RD0RC_0LD0LA_1LF0LA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB1RF_1LC0RD_0RB0LC_1RE1LD_1RA1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB---_0RC0LE_1RD1RA_1LB1RC_1RC0LF_0RF1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LF_0LA1LC_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB1LF_1RC1RA_1LD1RE_0RC0LD_0RA---_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LD_1LD1RA_0LF0RA_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB1RD_1RC1RB_1LA1LC_0RF1LE_0RD0LE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB0LF_0RC1RC_1RD1LA_1LE1LF_0RB0LE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB---_0RC0LB_1RD1RC_1LE1LD_1LA0LF_0RB0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LD0LF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1LD_1LF1RE_1LA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB1LB_0RC1LA_1RD1RC_1LE1LF_0RB0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB1RB_0RC1LD_1LA0RE_0LB1LB_---1RF_0LB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB1RD_1LC0RB_0RA0LC_1RE1RD_1RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_0LE0RC_0RE0LF_0RC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB1RA_1LC1LF_1RE0LD_0RE0LC_0RA---_1LB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB1RD_1LC0RD_0RA0LC_1RE1LF_1RA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB1RC_1LC0RB_0LA1RD_---0LE_1LF1LE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LA1RE_1LF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA1LF_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB---_0RC1RC_1RD1RC_1RE1LD_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB---_1RC1LD_1LD1RF_0RA0LE_0LD0RA_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB1LE_0RC1RD_0RD0LC_1LA1RF_0RB0LE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm177: ~halts (TM_from_str "1RB1RA_1LC1LE_0RA0LD_0RB1RD_0LF0LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm178: ~halts (TM_from_str "1RB1LF_1RC1RA_1LD1RE_0RC0LD_0RA---_0LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm179: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA1RB_0RD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm180: ~halts (TM_from_str "1RB0RA_1LC0LE_0LF0LD_1LE0RD_1RA0RB_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm181: ~halts (TM_from_str "1RB0RF_1RC---_1RD1LC_1LE1RA_0RF0LE_0RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm182: ~halts (TM_from_str "1RB---_1LC1LB_1LF0RD_1RE1RD_1RC0LB_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm183: ~halts (TM_from_str "1RB0LC_1LC0RD_0LE1RB_0RB0LD_0LF---_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm184: ~halts (TM_from_str "1RB1RC_0RC---_1RD0RD_1RE1LD_1LF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm185: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LF_1LE0RC_0RD0LE_1RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm186: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_---0LE_0RF0LF_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm187: ~halts (TM_from_str "1RB1LD_1RC---_1LC1RA_0LE0RA_1RE0LF_0RB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm188: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_0LE1LE_0RF1LA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm189: ~halts (TM_from_str "1RB---_1LC1LB_1RE1LD_0RE0LD_0RF1RF_1RA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm190: ~halts (TM_from_str "1RB---_1RC1LC_1LD1RF_0RA0LE_0LD0RA_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm191: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA0RD_1RA1RC_1LB1LF_1LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm192: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA1RB_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm193: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LC_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm194: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD1LC_0RE0LD_1RF---_0RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm195: ~halts (TM_from_str "1RB1RD_1RC0RF_0LA1LE_0LE1RB_0RB1LC_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm196: ~halts (TM_from_str "1RB1LD_1RC1RF_0RD---_1LE1LA_0RB0LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm197: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA1RE_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm198: ~halts (TM_from_str "1RB---_1RC0RC_1RD1LC_1RE1RB_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm199: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE0RA_1RF0LB_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm200: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE1LA_1LC0RB_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm201: ~halts (TM_from_str "1RB0LF_1RC---_0RD1RD_1RE1LF_1LA1LC_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm202: ~halts (TM_from_str "1RB1LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm203: ~halts (TM_from_str "1RB0LE_0RC0RF_1RD1RC_1LE1LD_1LB0LA_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm204: ~halts (TM_from_str "1RB1LD_1RC---_1LC1RA_0LE0RA_0RA0LF_0RD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm205: ~halts (TM_from_str "1RB1RF_1RC0LD_0RD0RF_1LE0RC_0LD1RA_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm206: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0LA_0LB0RE_1LF1RE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm207: ~halts (TM_from_str "1RB0RF_0LC0LF_1RC1LD_0LE1RF_1LC---_0RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm208: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB1RF_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm209: ~halts (TM_from_str "1RB0RC_1RC0RF_1LA0LD_1LD1LE_0LA1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm210: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RE1LF_1RF1RE_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm211: ~halts (TM_from_str "1RB0LB_0LC1RE_---1LD_0LE1LA_1RF0RA_1RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm212: ~halts (TM_from_str "1RB0LC_1LC0RD_0LE1RB_0RB0LD_0LF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm213: ~halts (TM_from_str "1RB0LE_1RC1LE_0LC1LD_0RF0RB_1LA1RD_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm214: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1LC---_1RF1RA_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm215: ~halts (TM_from_str "1RB1LA_1LA0RC_1LD1RC_---0LE_1RB0LF_0RE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm216: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD---_0RE0LD_1LF1LE_1RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm217: ~halts (TM_from_str "1RB0RD_1LC0LA_1LA0LC_1RE1RF_1RD---_0RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm218: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_1RF1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm219: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LC_1LA1RE_0RF0RD_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm220: ~halts (TM_from_str "1RB0LA_0RC1LF_1RD1RC_1RE1LD_1LA1LB_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm221: ~halts (TM_from_str "1RB0RF_1RC0LE_1LD1RC_1RC0LB_1RA1LE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm222: ~halts (TM_from_str "1RB1RC_0RC---_1LD1LF_0RA0LE_0RB0LD_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm223: ~halts (TM_from_str "1RB1LE_1LC1RD_0LE0RB_0LC0RD_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm224: ~halts (TM_from_str "1RB1RA_1RC0RB_0LC0LD_1LA1LE_0RB1LF_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm225: ~halts (TM_from_str "1RB0RB_0LB0RC_1LD1RC_1RC0LE_---0LF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm226: ~halts (TM_from_str "1RB1LC_1LC1RA_0LE1LD_1RE0RF_---0RA_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm227: ~halts (TM_from_str "1RB0LA_1RC---_1LD1LC_1LA0RE_1RF1RE_1RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm228: ~halts (TM_from_str "1RB1RA_1RC0RB_0LD0LE_---0LE_1LA1LF_0RB1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm229: ~halts (TM_from_str "1RB0LC_1LA1RA_1RD1LE_0RB0LA_0RD1LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm230: ~halts (TM_from_str "1RB1LD_1RC1RF_0LA0LE_0LE1LB_0RF1LA_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm231: ~halts (TM_from_str "1RB1LC_1LB1RA_---0LD_0RE0LE_0LF0RA_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm232: ~halts (TM_from_str "1RB---_0RC1RE_1RD1LF_1RE0LD_1LC1RD_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm233: ~halts (TM_from_str "1RB1LC_1LA1RD_1LA0LF_0LA0LE_0RE0RA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm234: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD---_0RB0LE_0RC0LD_1RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm235: ~halts (TM_from_str "1RB1LC_1LC1RA_1LF0LD_1RE0LC_0RA0LE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm236: ~halts (TM_from_str "1RB0LA_0LC0RB_1LA1LD_1LE1LD_1LF---_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LF0RE_0LA0RE_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm238: ~halts (TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0RA0LF_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm239: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0LA_1LC1RD_0RA1LE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm240: ~halts (TM_from_str "1RB1LA_0RC1RC_1RD0RA_1RE0LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm241: ~halts (TM_from_str "1RB0LB_0RC0LB_0RD1LA_1RE0LD_1RF---_1LC1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm242: ~halts (TM_from_str "1RB---_1LC1RF_1RE0LD_1LB1LD_0LA0RE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm243: ~halts (TM_from_str "1RB0LF_1LC0RE_0RD0LC_1LA---_1RA1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm244: ~halts (TM_from_str "1RB0RF_1LC0LB_1LD1LB_0RE0RA_0LB1RD_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm245: ~halts (TM_from_str "1RB1LB_1RC1LC_1LA0RD_---1RE_0LF1RC_0LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm246: ~halts (TM_from_str "1RB1LC_0LC1RF_1LD1LB_1LE0RF_1LA---_0LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm247: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE0RC_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm248: ~halts (TM_from_str "1RB0LA_0LC0RB_1LA1LD_1LE1LF_1LC1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm249: ~halts (TM_from_str "1RB1LA_0RC1LC_1RD1RC_1RE0LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm250: ~halts (TM_from_str "1RB1RF_0RC0LB_1LB0RD_1RE---_1RC1LF_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm251: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_0RE1RE_0LF1RB_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm252: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RD_1LA1LF_1LD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm253: ~halts (TM_from_str "1RB---_1LC0RE_0RA1LD_1RE0LC_1RF1RD_0RA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm254: ~halts (TM_from_str "1RB1RA_0LC1LD_1LA1LC_---1LE_1RF1LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm255: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA1RB_0RF1LA_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm256: ~halts (TM_from_str "1RB0LD_1LC0RE_1RA0LD_1LB1LA_1RC1RF_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm257: ~halts (TM_from_str "1RB1RE_1LC0RB_0LA0LD_1LA1LD_1RF1RE_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm258: ~halts (TM_from_str "1RB---_0RC0LD_0RD0RB_1LE0LA_1LF0LA_1LC0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm259: ~halts (TM_from_str "1RB0RD_1LC0RE_0LC1RA_0RB0RD_0RF---_1LF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm260: ~halts (TM_from_str "1RB1LE_1RC---_1RD0RD_1LA1RE_1RB0LF_0RB0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm261: ~halts (TM_from_str "1RB1LA_1RC1RF_1RD---_1LE0RD_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm262: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1LE0LF_1RA1RE_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm263: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB1LD_1RD0RE_---0LC_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm264: ~halts (TM_from_str "1RB1LF_1LC1RA_0RD0LC_0RE---_1RA1RC_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm265: ~halts (TM_from_str "1RB0LC_1LA1RB_0RA0LD_1RE1LD_0RB0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm266: ~halts (TM_from_str "1RB0LA_0LC0RB_1LE1LD_1LC1RF_1LA1LD_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm267: ~halts (TM_from_str "1RB---_0LC0RB_0LE1LD_1LC1LA_1LF1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm268: ~halts (TM_from_str "1RB0RD_1LC0RF_1LE0RD_0LE0RB_0LA1LD_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm269: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD0RB_0RC0LD_1LF1LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm270: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1RA_1RE---_1LF0RA_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm271: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_1LF1LD_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm272: ~halts (TM_from_str "1RB1RA_0RC0LD_1LB1RC_0RA1LE_1LF0RC_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm273: ~halts (TM_from_str "1RB0RA_0LC0LF_0RA0LD_1LE1LF_1RA1RE_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm274: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1LF1RD_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm275: ~halts (TM_from_str "1RB---_0RC1RE_1LD1RA_0RB0LF_1RC0RE_1LD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm276: ~halts (TM_from_str "1RB1LD_1RC0LB_1LA1RB_0RE0LD_1RF---_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm277: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1LA_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm278: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_0LF0LE_1RC0LD_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm279: ~halts (TM_from_str "1RB1RA_0RC1LE_1LD---_1LB0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm280: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD1LC_0LB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm281: ~halts (TM_from_str "1RB1LB_1RC1LF_1LD0RB_---0LE_0LD1RA_0LB0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm282: ~halts (TM_from_str "1RB0RB_1LC1RB_1RB0LD_1RC0LE_1RF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm283: ~halts (TM_from_str "1RB1RA_1LC1RC_0LE1LD_0LB0RD_1LA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm284: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1LC---_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm285: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RE_1LB0RD_1RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm286: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RE_0RB0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm287: ~halts (TM_from_str "1RB0LA_0RC1LE_1RD1LC_1LA1LB_---0RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm288: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA1RB_0RD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm289: ~halts (TM_from_str "1RB0LB_0RC0RB_1RD1RC_1LE1LF_1LA0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm290: ~halts (TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0LF0RD_0RD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm291: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RF_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm292: ~halts (TM_from_str "1RB1RF_1LC1LF_0RD0LC_1RE---_0RA1RF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm293: ~halts (TM_from_str "1RB0LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm294: ~halts (TM_from_str "1RB1LA_1LC0LD_0LC1LD_1RE0RB_0RF0RA_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm295: ~halts (TM_from_str "1RB0LB_0LB0RC_0RD---_1RE1RD_1LF1LE_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm296: ~halts (TM_from_str "1RB1RD_1LC1LF_0RD0LC_1RE---_0RA1RA_1LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm297: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LF_0LA1RC_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm298: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1RE1RA_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm299: ~halts (TM_from_str "1RB1RC_1LA1LE_0RF0RD_0RB1LE_0LE0LA_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm300: ~halts (TM_from_str "1RB---_0RC0LB_0RD0LF_1RE1RD_1LB1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm301: ~halts (TM_from_str "1RB1LC_0LA0RE_1LD0RD_1LA1LA_0RF0LA_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm302: ~halts (TM_from_str "1RB0LC_0RC---_1LC0LD_1RE1LE_0RF1RA_1LD0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm303: ~halts (TM_from_str "1RB1LE_1RC0RD_1LD1RC_---0LE_0RB0LF_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm304: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LA1RE_0RC0RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm305: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA1RB_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm306: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RD0RF_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm307: ~halts (TM_from_str "1RB1LE_0RC---_1LD1RA_0RA0LD_0LD0LF_0LF0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm308: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB1RB_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm309: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD0RE_0RC0LD_1RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm310: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA0RF_0RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm311: ~halts (TM_from_str "1RB---_1LC1RF_1RE1LD_0RE0LD_0RF0RC_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm312: ~halts (TM_from_str "1RB0LD_1RC0LD_1LA0RE_1LC1LB_1RA1RF_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm313: ~halts (TM_from_str "1RB1RA_1LC1LE_1RD0LC_0RA0RA_1LF1LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm314: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1RE1LA_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm315: ~halts (TM_from_str "1RB---_1LC1LB_1RF1LD_0RE0LD_0RF1RE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm316: ~halts (TM_from_str "1RB1LF_1LC1RE_0RD0LC_0RE---_1RA1RC_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm317: ~halts (TM_from_str "1RB0LA_1LC0RB_1LE1LD_1LA1RE_1RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm318: ~halts (TM_from_str "1RB1RA_1RC0LE_1LD0RB_0RC0LD_1LF1LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm319: ~halts (TM_from_str "1RB1RF_1LB1LC_1LD---_1LE0LD_0RE0RA_0LD1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm320: ~halts (TM_from_str "1RB1LC_1LC1RE_0LD0RA_0RA0LC_1RF1LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm321: ~halts (TM_from_str "1RB0LD_1RC1RA_1LB1RF_0RE1LA_1RE0RB_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm322: ~halts (TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RA1LF_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm323: ~halts (TM_from_str "1RB1LF_0LC0RD_0LD1LB_1LE0RB_1LA1RB_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm324: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD---_1LE1LA_0RB0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm325: ~halts (TM_from_str "1RB1RD_1LC---_0LC1RA_0RE0RF_1LE1LA_0RB0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm326: ~halts (TM_from_str "1RB1RD_1RC1LF_1LD1RF_0RE0LD_0RF---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm327: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LE_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm328: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LB_1LE1LA_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm329: ~halts (TM_from_str "1RB1RE_1LC1LF_0LA1RD_0RE0RB_0RD---_0LF0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm330: ~halts (TM_from_str "1RB1RF_1RC0RB_0LD1LC_---1LE_0RA0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm331: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD1LA_0RE0LD_1RF---_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm332: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LC_1RE1RA_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm333: ~halts (TM_from_str "1RB1RE_0RC0RB_0LD0LE_1LC---_1LF1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm334: ~halts (TM_from_str "1RB1LB_0RC---_1RD1RC_1RE1LD_1LF1LA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm335: ~halts (TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RA0LA_1RA0LF_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm336: ~halts (TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LE0RB_0RC0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm337: ~halts (TM_from_str "1RB0LB_1RC1LB_0LA0RD_0LA0RE_1LC1RF_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm338: ~halts (TM_from_str "1RB1LB_1LC1LA_1RE0LD_0RE0LC_0RF---_1RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm339: ~halts (TM_from_str "1RB1LB_1LC0RD_1LA1LA_---1RE_0LF1RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm340: ~halts (TM_from_str "1RB0LF_1LC0RD_0RA0LC_1RA0LE_0LA---_1RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm341: ~halts (TM_from_str "1RB0LC_1LA1RD_0RB1LF_---0RE_0LA1RE_0RD1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm342: ~halts (TM_from_str "1RB1RD_1LC0LF_---0RD_1LF1RE_0LC0LA_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm343: ~halts (TM_from_str "1RB---_0RC0RD_1LA1RD_1LB1LE_0LF0RB_0LE1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm344: ~halts (TM_from_str "1RB0LA_1RC1LF_1LD1LC_---0RE_0RF1RE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm345: ~halts (TM_from_str "1RB1RE_1RC---_1LD0RE_0RA0LD_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm346: ~halts (TM_from_str "1RB1RE_0RC1RA_1LD1LC_0RA0LD_1RC1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm347: ~halts (TM_from_str "1RB0LD_0RC1RE_1LC0LA_0LF1LA_0RA0LE_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm348: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA0RE_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm349: ~halts (TM_from_str "1RB0LF_0RC1LD_1RD---_1RE1RD_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm350: ~halts (TM_from_str "1RB0LC_1LC0RB_1RA0LD_1LE0RD_1LF---_0RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm351: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0LA_1LC0RE_1LF1RE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm352: ~halts (TM_from_str "1RB0LA_0RC0LD_1LA0LF_---0RE_1RC1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm353: ~halts (TM_from_str "1RB1RA_1LC0LE_1RD0LC_0RB0LF_1LF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm354: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0RC_1LA1RE_0RF0RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm355: ~halts (TM_from_str "1RB1RF_0RC0LB_0RD---_1RE1LF_1LB1RC_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm356: ~halts (TM_from_str "1RB0RF_0LC1LC_1LE0LD_1LB---_1RF1RA_1LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm357: ~halts (TM_from_str "1RB1RD_0RC0RE_1LD---_0LD1RA_1LF0RB_1LE0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm358: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA0LE_1RF---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm359: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA1RB_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm360: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LF_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm361: ~halts (TM_from_str "1RB1LF_1LC1RA_1RE0LD_0RB0LC_---0RA_0LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm362: ~halts (TM_from_str "1RB0LD_0RC1RC_1RD1RA_0LE1LE_0RF1LA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm363: ~halts (TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA0RA_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm364: ~halts (TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_1LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm365: ~halts (TM_from_str "1RB1RF_1RC1LF_1LD0RE_0RE0LD_0RB---_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm366: ~halts (TM_from_str "1RB1LA_0RC1LC_1RD1RC_1LE1RF_0RA0LE_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm367: ~halts (TM_from_str "1RB1RA_1RC0LE_1LD0RE_0RC0LD_1RA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm368: ~halts (TM_from_str "1RB1RF_1RC---_1RD1LC_1LE1LA_0RF0LE_0RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm369: ~halts (TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_0LA0LF_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm370: ~halts (TM_from_str "1RB1LF_1LC1RA_1RE0LD_0RB0LF_---0RA_0LE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm371: ~halts (TM_from_str "1RB1RA_0LC1LD_1LA1LC_---1LE_1RF1LB_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm372: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1LD_1LA1RF_---0RF_1LC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm373: ~halts (TM_from_str "1RB0LE_1LC0RA_0LF0LD_1LE1RD_0RB1RA_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm374: ~halts (TM_from_str "1RB1LC_0RC0LB_0RD0LB_1RE0LD_1RF---_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm375: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA1RF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm376: ~halts (TM_from_str "1RB0LB_0LC1RE_---1LD_1LE1RF_1RD1LF_0RA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm377: ~halts (TM_from_str "1RB1LD_0RC0LD_0LD0RE_1LA1RB_---0RF_0LB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm378: ~halts (TM_from_str "1RB0RE_0LC1LF_1RC0RD_1LB1RA_0LB1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm379: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE1LF_1LC1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm380: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LC_0LE1RD_1LA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm381: ~halts (TM_from_str "1RB1RA_1LC1LE_1RD0LC_0RA0LF_1LD1LE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm382: ~halts (TM_from_str "1RB1LA_0LB0RC_1RD0RD_1LE1RD_---0LF_1RC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm383: ~halts (TM_from_str "1RB1LA_1RC0RC_0LA1RD_0LA0LE_---1LF_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm384: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LB_1LA1RE_0RF0RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm385: ~halts (TM_from_str "1RB---_1RC0LE_1LD0RB_0RC0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm386: ~halts (TM_from_str "1RB1LC_0RC0RF_1LD1LA_1LE---_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm387: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LF_0RB1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm388: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RA1RF_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm389: ~halts (TM_from_str "1RB1RC_1LA1LD_0RC0RB_0LF0LE_0LA1RC_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm390: ~halts (TM_from_str "1RB---_0RC0RA_0LD0RB_0LE0LF_1RC1LD_1LE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm391: ~halts (TM_from_str "1RB1LE_1LC1RA_0RA0LD_1RC0LE_0LF0LD_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm392: ~halts (TM_from_str "1RB1RA_1LB1RC_1LA1LD_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm393: ~halts (TM_from_str "1RB1LE_1LC0RB_1LF1RD_---0LA_1LA1RF_1RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm394: ~halts (TM_from_str "1RB---_0RC1RC_1RD1RF_1LE0LF_0RA0LE_1RC1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm395: ~halts (TM_from_str "1RB1LC_0LC0LF_---0RD_1RE1RD_1LE1LF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm396: ~halts (TM_from_str "1RB1LA_1RC1RF_1RD---_1LE0RF_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm397: ~halts (TM_from_str "1RB1LC_1LA1RC_0LD0LA_1LE0RE_0RF1LB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm398: ~halts (TM_from_str "1RB1RC_0RC---_1RD1LE_1RE1LD_1LF1RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm399: ~halts (TM_from_str "1RB---_0RC1RC_1RD1RA_1LE1LF_0RA0LE_1LB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm400: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1RD_1LF1LE_1LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm401: ~halts (TM_from_str "1RB0LB_1LC1LD_---1RA_1LE1RF_1RD1LF_0RA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm402: ~halts (TM_from_str "1RB1LC_1LA1LC_1LB1RD_---0RE_0LB0RF_0RD0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm403: ~halts (TM_from_str "1RB1LD_1RC0RC_1LA1RD_1RF0LE_0RF0LD_1RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm404: ~halts (TM_from_str "1RB0RB_1LC0RC_0LA0LD_1RA0LE_1RF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm405: ~halts (TM_from_str "1RB1RA_1RC1RE_1LD0RB_0RC0LD_0LF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm406: ~halts (TM_from_str "1RB---_0RC1RC_1RD0LE_1RE1RC_1LF1LC_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm407: ~halts (TM_from_str "1RB0LD_1LC0LF_0LC1RA_---1RE_0RB0RE_1LF1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm408: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_0RE0LA_0LA0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm409: ~halts (TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA1RF_0LD1RD_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm410: ~halts (TM_from_str "1RB0LE_0RC0RA_0RD0LA_1LC1LD_0RA0LF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm411: ~halts (TM_from_str "1RB---_0RC1RC_1RD1RA_1LE1LF_1LB0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm412: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA1RE_0RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm413: ~halts (TM_from_str "1RB---_0LC0RB_0LE1LD_0LB1LA_1LF1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm414: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA---_0LA1LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm415: ~halts (TM_from_str "1RB---_0RC1LE_0RD1RC_1LA1LF_0RB0LE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm416: ~halts (TM_from_str "1RB1RA_1LC1LE_1RD0LC_0RA0RF_1LF1LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm417: ~halts (TM_from_str "1RB1RF_0LC0LD_1LC1LD_1LA1RE_0RB0RF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm418: ~halts (TM_from_str "1RB1RF_1LC0RD_0RA0LC_1RE---_1RA1LE_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm419: ~halts (TM_from_str "1RB1LC_0LA1LC_1LA1RD_1LB0RE_1RF0RD_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm420: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA1RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm421: ~halts (TM_from_str "1RB1LF_0RC1LA_1LD1RE_0LD1RE_1RF---_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm422: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA0RE_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm423: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1LD_1LA0RF_1LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm424: ~halts (TM_from_str "1RB---_1LC1RE_0RA0LD_0RA0LF_1RA1LC_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm425: ~halts (TM_from_str "1RB1LD_0LC1LE_1RE0LD_1LC0RB_0RF0RA_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm426: ~halts (TM_from_str "1RB0LD_0RC1RE_1LD---_0RB0LD_1RF1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm427: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LE1RA_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm428: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA---_0LA1LF_0RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm429: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LE1RB_0LF---_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm430: ~halts (TM_from_str "1RB---_0RC0LB_1RD1LF_1RE0LD_1LC1RD_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm431: ~halts (TM_from_str "1RB0RF_1LC1LE_0RE1LD_0LB1RC_0LD0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm432: ~halts (TM_from_str "1RB1LA_1LC0RD_0RB0LC_1RF1LE_1RD1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm433: ~halts (TM_from_str "1RB1RA_1RC0RB_1LD0RD_---0LE_0LF0RA_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm434: ~halts (TM_from_str "1RB0LD_1RC1RC_0LA1RA_1LF1LE_1LA0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm435: ~halts (TM_from_str "1RB0LA_1LC0RF_1LF1LD_1LE---_1LA1RB_1RA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm436: ~halts (TM_from_str "1RB1LB_1LB1RC_1RF1LD_0RF0LE_0LD0RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm437: ~halts (TM_from_str "1RB1RD_1LC0RF_0RD0LC_1RE0RE_1RA1LE_1RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm438: ~halts (TM_from_str "1RB0RB_0LC0RF_1LC1LD_0LE1RB_1LA---_0RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm439: ~halts (TM_from_str "1RB1LC_0LA0RB_1RD---_1LA1LE_1LF0LF_1LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm440: ~halts (TM_from_str "1RB0RC_0RC0LD_1LD0RE_0LA1LB_---1RF_0LB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm441: ~halts (TM_from_str "1RB1LB_1LC0LB_---0RD_1LF1RE_1RD0LC_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm442: ~halts (TM_from_str "1RB1LF_0RC---_1RD1RA_1RE1RD_1LC1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm443: ~halts (TM_from_str "1RB0RE_0RC0RF_0LD1RE_1LD0LA_1LA0LD_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm444: ~halts (TM_from_str "1RB0LE_1RC---_1LD1RF_0RF1LE_0RC0LA_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm445: ~halts (TM_from_str "1RB1RA_1RC1RC_0LD0RC_0LB1LE_1LF1LD_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm446: ~halts (TM_from_str "1RB1LA_1RC1RF_0RD---_1LE1LA_0RB0LE_1RD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm447: ~halts (TM_from_str "1RB0RE_1RC1LD_0LB0RC_0LF0LA_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm448: ~halts (TM_from_str "1RB---_0RC1RC_1RD1LF_1LE1LB_0RA0LE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm449: ~halts (TM_from_str "1RB1RA_1RC0LE_1LD0RB_0RC0LD_1RA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm450: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA1RF_0RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm451: ~halts (TM_from_str "1RB0LE_1LC1RD_0RB0LC_0RE1RE_0RF1LA_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm452: ~halts (TM_from_str "1RB1RF_1RC---_1RD1LC_1LE1LF_0RF0LE_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm453: ~halts (TM_from_str "1RB---_0RC1LC_1RD1RC_1RE1LD_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm454: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm455: ~halts (TM_from_str "1RB1LE_1LC0RB_0LE0RD_---0LE_1LA1RF_0RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm456: ~halts (TM_from_str "1RB1RF_1RC0LE_1LD0RB_0RC0LD_1RA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm457: ~halts (TM_from_str "1RB1LC_1LA1RC_1LD0RF_1LE---_1LA0LA_0LD0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm458: ~halts (TM_from_str "1RB1RA_0RC0RB_1RD0LC_0LE---_1LF1LD_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm459: ~halts (TM_from_str "1RB0LF_1LC1RA_1LE1RD_1LC0RB_0RC0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm460: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RD_1LA1LF_1LD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm461: ~halts (TM_from_str "1RB1RE_0RC1LF_1LD1LC_0RA0LD_1RC---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm462: ~halts (TM_from_str "1RB0RD_1LC0RE_0RB0LD_1RA0LF_1RD---_0LC0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm463: ~halts (TM_from_str "1RB0LD_1RC1LD_1LD1RA_---0LE_0LA0LF_0RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm464: ~halts (TM_from_str "1RB0RB_1LC1RB_---0LD_1RA0LE_1RF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm465: ~halts (TM_from_str "1RB1RA_0RC0RE_1LD---_0LD1RA_1LF0RB_1LE0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm466: ~halts (TM_from_str "1RB0LA_1RC1LA_1RD1LE_1LC0RB_---0LF_0LC0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm467: ~halts (TM_from_str "1RB0LD_1RC1LD_1LD1RF_0LC1LE_---0LA_0RC1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm468: ~halts (TM_from_str "1RB1RA_1RC0RB_1LD0RD_---0LE_0LF0LE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm469: ~halts (TM_from_str "1RB1RE_1RC0RF_1LD1LC_0RE0LD_0RC1RA_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm470: ~halts (TM_from_str "1RB1RE_1LC1LB_---0RD_0RE1RD_1LF1LA_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm471: ~halts (TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE0LE_1LC1RE_1RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm472: ~halts (TM_from_str "1RB1LB_1LC1LA_0LA1RD_---0RE_1LE0RF_0RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm473: ~halts (TM_from_str "1RB1LE_1LC0RB_0LA1RD_---0LA_1LA1RF_1RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm474: ~halts (TM_from_str "1RB1LD_1RC---_1LC1RA_0RD0LE_0RB0LF_0LD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm475: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB1LC_0LF1RB_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm476: ~halts (TM_from_str "1RB0LF_1LC1RA_1LE1RD_0RB0LC_0RC0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm477: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE0LD_1LA0RB_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm478: ~halts (TM_from_str "1RB0RC_1RC0LF_1RD0RD_1LE1RD_---0LB_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm479: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LB_1LA1RD_1LF1LA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm480: ~halts (TM_from_str "1RB1LE_1LC0RF_0LA1RD_---0LA_1LA1RB_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm481: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD0RA_0RE0LD_1LB---_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm482: ~halts (TM_from_str "1RB1LD_1LC1RA_0RA1RA_0LF0LE_1RC0LD_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm483: ~halts (TM_from_str "1RB1RA_0LC0RE_1LE1LD_1LA1LF_0LA0RB_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm484: ~halts (TM_from_str "1RB---_1RC1LB_1LD1RE_0RE0LD_0RC1RF_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm485: ~halts (TM_from_str "1RB0RE_0RC---_1LD0RF_0LA1LA_0LB0LD_1LE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm486: ~halts (TM_from_str "1RB---_1RC1LC_1LD1RE_0LF0RE_1RA1LD_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm487: ~halts (TM_from_str "1RB1RF_0LC0RB_0LD1LC_1LE---_1LA1LE_1RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm488: ~halts (TM_from_str "1RB1LF_0RC---_1RD1RC_1LE1LD_1LB1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm489: ~halts (TM_from_str "1RB1RD_0RC---_0RD1LE_1LB0RC_0LF1RA_0LE1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm490: ~halts (TM_from_str "1RB0LC_1LA1RB_0RA0LD_1RE1LD_1RA0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm491: ~halts (TM_from_str "1RB1LC_1LC1RA_---0LD_0RE0LE_0LF0RA_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm492: ~halts (TM_from_str "1RB---_0RC1LF_1RD0LC_1RE---_1LB1RC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm493: ~halts (TM_from_str "1RB0RD_1LC1LF_0RA1LB_0LA0RE_---1RA_0LC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm494: ~halts (TM_from_str "1RB0RE_0RC---_1LD0RF_0LA1LA_1LD0LD_1LE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm495: ~halts (TM_from_str "1RB1LE_1LC---_0RD0LC_0RE1LA_1RF1RD_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm496: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RA_0LE0LF_0RA0LE_0LF0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm497: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA0RE_0LD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm498: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LF_1LA---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm499: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1LA_1LE1RF_0RD0LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm500: ~halts (TM_from_str "1RB1LD_1LC0RB_1RC0LD_1LE0LF_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm501: ~halts (TM_from_str "1RB1LF_1LC0RD_0RA0LC_1RE---_1RA1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm502: ~halts (TM_from_str "1RB0LD_1LC0RD_0RB0LC_1LE1LD_0RF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm503: ~halts (TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA---_0LD1RF_1LA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm504: ~halts (TM_from_str "1RB---_0RC1LD_1RD1RC_1RE1LB_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm505: ~halts (TM_from_str "1RB1RC_0RC0RE_1LD1LF_0RA0LD_1LF---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm506: ~halts (TM_from_str "1RB1LD_1RC---_1RD1LC_1LE1RF_0RF0LE_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm507: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LC_1LA1RE_0RF0RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm508: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD1RE_0RC0LD_0RA---_1RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm509: ~halts (TM_from_str "1RB1RF_1RC0LE_1RD0LE_1LB0RA_1LD1LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm510: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm511: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD0LE_0LB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm512: ~halts (TM_from_str "1RB1LD_1LC1RA_---0RA_1LE0LD_1RF0LC_1LE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm513: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA0RD_0RF1LA_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm514: ~halts (TM_from_str "1RB0LE_0RC0RD_1LD0LA_1LC1RD_0RF1LE_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm515: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA1RC_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm516: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE1LC_0RF---_0RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm517: ~halts (TM_from_str "1RB1RE_1LC---_0LD0LC_1RD0RE_1LC1RF_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm518: ~halts (TM_from_str "1RB0LB_0RC1LE_1RD1LF_1LA1RC_---0RA_0LB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm519: ~halts (TM_from_str "1RB1LF_1LC0RD_0RD0LC_0RE---_1RA1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm520: ~halts (TM_from_str "1RB---_0RC1RF_1RD1LC_1LE1LD_0RA0LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm521: ~halts (TM_from_str "1RB1LF_1RC1RE_1LD0RE_0RA0LD_1RA1LA_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm522: ~halts (TM_from_str "1RB1RA_1LC1RE_---0LD_0RA0LF_1LA1LC_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm523: ~halts (TM_from_str "1RB1LC_1LA1RC_0LD0LA_1LE0RE_1RF1RA_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm524: ~halts (TM_from_str "1RB1RA_0LC0RB_1LF1LD_0RE---_1LA1LE_0LA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm525: ~halts (TM_from_str "1RB1LB_0RC1LD_1LA0RE_0LB1LB_---1RF_0LB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm526: ~halts (TM_from_str "1RB1LE_1RC0RF_1RD0RC_0LE1RD_1LF0LA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm527: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB1RD_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm528: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD0RE_0RB0LD_1RA1LB_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm529: ~halts (TM_from_str "1RB0LA_1RC1RF_1LD1LC_---0RE_0RF1RE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm530: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1RF_0RB0LA_0RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm531: ~halts (TM_from_str "1RB---_1LC0LF_---0RD_1LD1RE_1RD1LF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm532: ~halts (TM_from_str "1RB1LC_0LA0RF_1LD1RB_1LE---_1LA1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm533: ~halts (TM_from_str "1RB0LF_1LC1RE_1LD1RC_---0RE_0RB1LA_0LA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm534: ~halts (TM_from_str "1RB0RE_1LC1LF_---1LD_0RE0LD_1RA1RF_1RE0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm535: ~halts (TM_from_str "1RB---_0RC1LF_1RD1RC_1LE1LB_0RB0LE_1LA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm536: ~halts (TM_from_str "1RB1LD_0RC1LF_1RD1RC_1LE1LA_0RB0LE_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm537: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE1LD_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm538: ~halts (TM_from_str "1RB1LC_0LA1LC_1LA1RD_1LB0RE_0RF0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm539: ~halts (TM_from_str "1RB1LB_1RC---_0RD1RD_1RE0RA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm540: ~halts (TM_from_str "1RB1LF_0RC0LF_1RD---_1RE0RE_1LA1RF_1RC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm541: ~halts (TM_from_str "1RB0LB_1RC0LE_1RD0RD_1LA1RD_1RF1LE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm542: ~halts (TM_from_str "1RB---_0RC1LE_0RD1RC_1LA1LF_0RB0LE_1LD0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm543: ~halts (TM_from_str "1RB1LE_0LC1RF_1LA1LD_0LE---_1LC0RE_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm544: ~halts (TM_from_str "1RB---_1RC1LB_1RD1LF_1LE0RA_0RC0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm545: ~halts (TM_from_str "1RB1RC_0RC1RE_1LD1LF_0RA0LD_1RC---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm546: ~halts (TM_from_str "1RB---_1LC1LB_1LF0RD_1RE1RD_1RC0RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm547: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1RA_1RE---_1LF0RB_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm548: ~halts (TM_from_str "1RB1LF_1RC1LB_1RD1RA_1LE0RA_0RC0LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm549: ~halts (TM_from_str "1RB1RD_1LC0RD_1LE0LD_0LC0RB_0LF1LF_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm550: ~halts (TM_from_str "1RB1RD_1LC0RB_0RA0LC_1RE1RA_1LF1LE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm551: ~halts (TM_from_str "1RB0LA_0RC1RC_1RD1LA_1LE1LB_---0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm552: ~halts (TM_from_str "1RB0LF_0RC1LE_0RD---_1LA1LD_1RD1RE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm553: ~halts (TM_from_str "1RB1RE_0LC0LA_1LF1LD_1LA1RB_0RE0RB_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm554: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_---0RE_0LA0RF_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm555: ~halts (TM_from_str "1RB0RA_0LC1LC_1LE0LD_1LB---_1RA1RF_1LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm556: ~halts (TM_from_str "1RB1RD_0LC0RB_1LA1LC_0RF0RE_0LA1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm557: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1RF_1LE0RB_0RD0LE_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm558: ~halts (TM_from_str "1RB0LE_1LC0RC_0RD0LC_0RE---_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm559: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA1RB_0RF1LF_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm560: ~halts (TM_from_str "1RB1LE_1LC0RF_1RD0LC_0RA---_1LB1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm561: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RA1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm562: ~halts (TM_from_str "1RB1LF_1LC1RA_1RD0LC_0LE0RA_---0RB_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm563: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_0RE0LD_0LA0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm564: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD1LA_1RE0RB_---0LA_0RE1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm565: ~halts (TM_from_str "1RB1RA_1LC1LF_1RE0LD_0RE0LC_0RA---_1LB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm566: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD0RE_1LA---_1LE0RF_1LD1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm567: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB1LC_0LF1RF_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm568: ~halts (TM_from_str "1RB---_1RC1LF_0RD0LE_1RE0LF_1LC1RA_0RC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm569: ~halts (TM_from_str "1RB---_1RC---_1LD0RE_1LB0RD_0RC1LF_0LF0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm570: ~halts (TM_from_str "1RB1LA_1RC1LF_1RD---_1LE0RA_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm571: ~halts (TM_from_str "1RB0RD_1LC0RE_0LC1RA_0RB0RD_0RF---_1LF1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm572: ~halts (TM_from_str "1RB0RF_1RC1RB_1LD1LC_0RE0LD_0RF1LA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm573: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm574: ~halts (TM_from_str "1RB1RE_1LC0RD_0RB0LC_1RA1RD_1LF---_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm575: ~halts (TM_from_str "1RB1LD_0RC1RF_1LC0LA_0LA0LE_0RB1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm576: ~halts (TM_from_str "1RB1RC_1LA1LE_0RC0RD_0RB1LF_0LF0LA_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm577: ~halts (TM_from_str "1RB1LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm578: ~halts (TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1LC1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm579: ~halts (TM_from_str "1RB0LA_0RC---_1RD1LE_1LA0RF_1LD1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm580: ~halts (TM_from_str "1RB1RA_1LC1LB_1LD0LC_0LE---_1RE1LF_0RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm581: ~halts (TM_from_str "1RB1RA_0LC0RB_1RE1LD_0LB---_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm582: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD---_1LE0LD_0RF0LE_0RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm583: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA0LD_0RE0LD_0RF---_1RA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm584: ~halts (TM_from_str "1RB0LF_1LC0RD_0RD0LC_0RE---_1RA1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm585: ~halts (TM_from_str "1RB0LF_1RC0RD_1RD---_1LE1RA_0RC1LA_0RE0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm586: ~halts (TM_from_str "1RB1LC_0LA0RF_1LD1RB_1LE---_1LA1RB_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm587: ~halts (TM_from_str "1RB0RD_1RC---_0LA1LA_0RE0LC_1LF1RE_1LB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm588: ~halts (TM_from_str "1RB1RE_1LC1LB_0RE0LD_0RB0LC_1RF1RA_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm589: ~halts (TM_from_str "1RB0LA_1RC1RE_1LD0LC_---0RB_1RF1LC_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm590: ~halts (TM_from_str "1RB1LF_1LC1RA_1RD0LC_1LE0RA_---1RD_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm591: ~halts (TM_from_str "1RB1RA_1LC0RC_0RD0LC_0RE---_1RF1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm592: ~halts (TM_from_str "1RB0LF_0RC1RA_1RD0LE_1LE---_0RA0LC_1LC1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm593: ~halts (TM_from_str "1RB0RA_0LC1LC_1LE1LD_1LB---_1RF1RA_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm594: ~halts (TM_from_str "1RB---_1RC0RC_1LD1RE_---1LE_1RA0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm595: ~halts (TM_from_str "1RB1RC_1LA1LE_0RF0RD_0RB1LD_0LE0LA_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm596: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LC_0LD1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm597: ~halts (TM_from_str "1RB0RD_1LC1LF_0LC1RA_0RB1LE_0LF---_0LE0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm598: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_1RF1RE_0LF0RC_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm599: ~halts (TM_from_str "1RB0RC_1LA---_1LC1RD_1RC1LE_1RA0LF_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm600: ~halts (TM_from_str "1RB---_1RC1LF_1LD1RB_1RE0LD_0RA0RC_1LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm601: ~halts (TM_from_str "1RB0RC_1RC0LD_1LB1RC_---0LE_1RF1LE_0RC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm602: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0LE_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm603: ~halts (TM_from_str "1RB---_0RC0LF_0RD0LB_1RE1RD_1LC1LE_1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm604: ~halts (TM_from_str "1RB0LE_0RC---_1RD1RC_1LA1LF_0RB0LA_0LB1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm605: ~halts (TM_from_str "1RB1RE_0RC0LF_0RD---_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm606: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_---0LE_0RA0LF_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm607: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LD_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm608: ~halts (TM_from_str "1RB1LD_1LC1RD_0LE0RD_1LE0RC_1LF---_1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm609: ~halts (TM_from_str "1RB1RD_0LC0RB_1LD1LC_0LE1RA_1LA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm610: ~halts (TM_from_str "1RB1LC_0LC0RB_0LE1LD_1LE1LD_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm611: ~halts (TM_from_str "1RB1RA_1LC1LE_1RD0LC_0RA1LF_1LD1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm612: ~halts (TM_from_str "1RB1LF_0RC1RC_1RD0LC_1RE---_1LA0RE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm613: ~halts (TM_from_str "1RB1RA_1LC1LF_0RD0LC_0RE---_1RA1RD_1LE1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm614: ~halts (TM_from_str "1RB1RC_0RC---_1LD1RA_0LE1LF_0RA0LE_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm615: ~halts (TM_from_str "1RB1LA_1LC1RD_0RD0LC_0RB1RE_1RF1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm616: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA0RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm617: ~halts (TM_from_str "1RB---_1LC1RE_0RE1LD_0RB0LF_1RF1RC_1RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm618: ~halts (TM_from_str "1RB0RF_0LC0LD_1RD1LD_0LE0RA_1LC---_0RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm619: ~halts (TM_from_str "1RB1RE_0RC1RA_1RD1RC_1LB1LD_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm620: ~halts (TM_from_str "1RB1RE_0LC0LA_1LC1LD_1LA1RF_0RB0RF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm621: ~halts (TM_from_str "1RB1LF_1LC0RE_0RD0LC_1LA---_1RA1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm622: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LF_1LA1RF_1LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm623: ~halts (TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_1LF0LF_1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm624: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0RE_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm625: ~halts (TM_from_str "1RB0RB_1RC---_0LC0LD_1RF0LE_0RF1LD_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm626: ~halts (TM_from_str "1RB0LF_1LC0RD_---1LA_0LA1RE_0LC1RD_0RB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm627: ~halts (TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LD_1LC1RE_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm628: ~halts (TM_from_str "1RB---_0RC1RC_1RD0RF_1LE0LF_0RA0LE_1LA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm629: ~halts (TM_from_str "1RB1RA_0LC1LD_1LA1LC_---0LE_1RE1LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm630: ~halts (TM_from_str "1RB1LE_1LC0RD_0RA0LC_1RE---_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm631: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LF_1LA---_1LA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm632: ~halts (TM_from_str "1RB1RE_1RC0LF_1LD---_0RE0LD_0RC1RA_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm633: ~halts (TM_from_str "1RB1RE_0RC0RA_1LC0LD_0RA0LC_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm634: ~halts (TM_from_str "1RB1RA_1RC1RD_0LB1LE_0LC0RD_1LF1LC_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm635: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1LD_1LA1RF_1LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm636: ~halts (TM_from_str "1RB0LF_1LC1RA_1LE1RD_0LD0RB_0RC0LE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm637: ~halts (TM_from_str "1RB---_0LC0RB_1LF1LD_1LE1LC_1LC1RE_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm638: ~halts (TM_from_str "1RB0LD_0RC0RE_1LC0LA_0RA1LD_---1RF_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm639: ~halts (TM_from_str "1RB1LA_1RC1RF_1RD---_1LE0RA_0RB0LE_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm640: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA0RD_0RF1LF_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm641: ~halts (TM_from_str "1RB1LD_1RC0RC_0LA1RE_---1LA_0LD0LF_0RB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm642: ~halts (TM_from_str "1RB1LE_1LC1RC_0RD0LC_0RE---_1RF1LA_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm643: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_1LF0LE_0RA1RD_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm644: ~halts (TM_from_str "1RB1RA_1LC1LB_0LF0LD_1RE0LC_0RA---_0LE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm645: ~halts (TM_from_str "1RB1LE_0LC0RB_1LF1RD_1LA0RD_1LD1RD_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm646: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LB_1LA1RD_1LD0LF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm647: ~halts (TM_from_str "1RB1RE_0RC1LF_1LD1LC_0RA0LD_0LF---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm648: ~halts (TM_from_str "1RB1LB_0RC0RB_1RD0LE_1LA1RF_0LD0RA_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm649: ~halts (TM_from_str "1RB1RF_1LC0LF_0RD0LC_1RE---_0RA0LA_1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm650: ~halts (TM_from_str "1RB1LC_1LB1RA_0LD0RA_0RA0LE_---0LF_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm651: ~halts (TM_from_str "1RB1RD_1LC0RD_0RA0LC_1RE1LF_1RA1LE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm652: ~halts (TM_from_str "1RB0LF_0RC1RC_1RD1LA_1LE1LF_0RA0LE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm653: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RE_1LB0RD_0RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm654: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LD1LF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm655: ~halts (TM_from_str "1RB0LD_1RC1RA_0LD1RE_0RE1LA_1LD1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm656: ~halts (TM_from_str "1RB0RB_1LC0LD_0LC1RA_1LD1LE_---1RF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm657: ~halts (TM_from_str "1RB1LD_1RC0LB_1LA1RB_0RE0LD_1RF---_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm658: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LB_1LA1RF_---0LC_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm659: ~halts (TM_from_str "1RB1LE_1LC1RA_---0LD_0RA1RD_0LF0LE_0LC0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm660: ~halts (TM_from_str "1RB1RD_1LC1RE_---0LD_0RA0LF_1RA1LC_0LC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm661: ~halts (TM_from_str "1RB1LD_1RC1RE_1LC1RA_0LF0LB_0RA0LD_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm662: ~halts (TM_from_str "1RB0LB_1LC1LA_0RD1LB_1RB0RE_0LA0RF_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm663: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LA0RE_1LF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm664: ~halts (TM_from_str "1RB1RF_0RC---_1LD1LC_1LE1LC_0RF0LE_0RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm665: ~halts (TM_from_str "1RB0RC_0RC0RF_1LD0RE_0LA1LB_1LF1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm666: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RE1LD_1RF1RE_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm667: ~halts (TM_from_str "1RB---_0RC0LB_1RD1RC_1LE1LD_1LA0LF_0RB0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm668: ~halts (TM_from_str "1RB0LB_0RC1LA_1RD1RF_1LE1RC_0RB0LE_0RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm669: ~halts (TM_from_str "1RB1RE_0RC1LD_1LA1LD_0LD0LA_0RF---_0RE0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm670: ~halts (TM_from_str "1RB---_1LC1RF_0RA0LD_0RE0LE_0LC0RA_1RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm671: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_0LE0RD_0RA0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm672: ~halts (TM_from_str "1RB1RE_1RC0LF_1LD---_0RE0LD_0RC1RA_0LE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm673: ~halts (TM_from_str "1RB0LF_0LC0RB_1LA1RD_1LE1LD_1LC1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm674: ~halts (TM_from_str "1RB0RF_1LB0LC_1LD---_1RE0RA_1RA0RE_1LC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm675: ~halts (TM_from_str "1RB0LF_1LC0RE_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm676: ~halts (TM_from_str "1RB1LA_1RC1LF_1LD1RE_0RC0LD_0RA---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm677: ~halts (TM_from_str "1RB0RB_0RC1LE_1LD1LF_0LD1RA_0LF0RA_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm678: ~halts (TM_from_str "1RB1LA_0RC1LB_1RD1RC_1RE0LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm679: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LD_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm680: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA0RE_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm681: ~halts (TM_from_str "1RB1LE_1LC1LB_---0RD_0RE1RD_1LF1RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm682: ~halts (TM_from_str "1RB1LF_1LB1RC_0LD0RC_1LE---_0LA1LA_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm683: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE0LF_1RA1RD_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm684: ~halts (TM_from_str "1RB1RF_1LC0RF_1LD0LB_0LE1LE_1LA---_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm685: ~halts (TM_from_str "1RB1LF_0RC1LA_1LD1RD_0LD1RE_1RF---_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm686: ~halts (TM_from_str "1RB1RA_1RC1LA_1LC1LD_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm687: ~halts (TM_from_str "1RB0LF_1RC1RA_1RD0RD_1RE---_0LE0LA_0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm688: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RA1RF_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm689: ~halts (TM_from_str "1RB1LC_1LC1RF_0RE0LD_0LC0RD_1RA---_1RE1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm690: ~halts (TM_from_str "1RB0LE_0RC1LE_1LD1RA_0RA0LD_1RC0LF_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm691: ~halts (TM_from_str "1RB1LF_0LC0RB_1LD1RC_0LE1RD_1LA1LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm692: ~halts (TM_from_str "1RB1LC_0LA0RE_1RD1RB_1LA1LD_0RF0LA_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm693: ~halts (TM_from_str "1RB1LE_1LC1RD_0RD0LC_0RE---_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm694: ~halts (TM_from_str "1RB1LC_0RC---_1RD1RC_1RE1LD_1LF1RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm695: ~halts (TM_from_str "1RB1LF_1LC1RA_1RE0LD_0RB0LD_---0RA_0LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm696: ~halts (TM_from_str "1RB0LB_1LC1RF_0RD0LC_1RE---_0RA1RA_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm697: ~halts (TM_from_str "1RB1LB_1RC0LD_1LB1RA_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm698: ~halts (TM_from_str "1RB1RD_1RC---_0RD1LC_1RE1RA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm699: ~halts (TM_from_str "1RB0LD_1RC1LD_1LD0RB_0LA0LE_0LF1RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm700: ~halts (TM_from_str "1RB0LF_0LC0LF_1RC1LD_0LE1RF_1LC---_0RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm701: ~halts (TM_from_str "1RB1LB_0RC0LB_0RD---_1RE1RA_1RF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm702: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA1RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm703: ~halts (TM_from_str "1RB1LD_1LC1LE_0RA1RA_1RF0LE_0RF0LD_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm704: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LA1RE_1RA0RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm705: ~halts (TM_from_str "1RB1LC_1LC1RA_0LF0LD_1RE0LC_1LE1RF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm706: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm707: ~halts (TM_from_str "1RB0RA_0LC0LD_1LF0LD_1RE1LC_1RA0RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm708: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RD1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm709: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1RD_1LF1LE_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm710: ~halts (TM_from_str "1RB---_0RC0LB_0RD0LC_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm711: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA0RF_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm712: ~halts (TM_from_str "1RB1RE_0RC0LB_0RD---_1RE1LD_1LB1RF_1RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm713: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA0LE_1RD---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm714: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD1RE_0RC0LD_0RA---_1RA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm715: ~halts (TM_from_str "1RB1RF_0RC1LA_0RD---_1LE1LD_0RB0LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm716: ~halts (TM_from_str "1RB---_1RC1LB_0RD0RC_1LE0RF_0LE0RB_1LF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm717: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RE_0LA0RD_0RF0LB_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm718: ~halts (TM_from_str "1RB1RE_1LC1RD_1LD0LC_0RB0RE_1LF1RA_---0LA") c0.
Proof. solve_loop1_0 2000%N. Time Qed.

Lemma tm719: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RA_0RB0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm720: ~halts (TM_from_str "1RB0LA_0RC1RC_1RD1LA_1LE1LB_---0LF_0RB0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm721: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LB---_0LF1RF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm722: ~halts (TM_from_str "1RB1RA_1RC1RF_0LD---_1LE1LD_1LA0LD_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm723: ~halts (TM_from_str "1RB1LF_0LC0RD_0LD1LC_1LE0RB_1LA1RB_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm724: ~halts (TM_from_str "1RB0RD_0LC1RD_1RA1LC_0LC0LE_0RA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm725: ~halts (TM_from_str "1RB1LE_1LC1RD_1RD0LB_---0LA_1LA1RF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm726: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE---_0RF1RA_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm727: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1LB_1LA1RF_---0LF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm728: ~halts (TM_from_str "1RB---_1RC0LB_1LD1RB_1RE1LE_0RA0LF_0RD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm729: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0RF_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm730: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA0RE_0LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm731: ~halts (TM_from_str "1RB1RE_1LC0RB_0RD0LC_1RA1RE_1RD1LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm732: ~halts (TM_from_str "1RB1LA_1RC1RF_1RD---_1LE0RA_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm733: ~halts (TM_from_str "1RB0LA_1RC1RF_0RD---_1LE1LA_1LB0LE_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm734: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD0RC_1RE0RB_---0LA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm735: ~halts (TM_from_str "1RB1LE_1LC0RF_1LF1RD_---0LA_1LA1RB_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm736: ~halts (TM_from_str "1RB1LA_1LC0RD_---1RA_0LF0RE_1LF1RE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm737: ~halts (TM_from_str "1RB1LF_1RC1LD_0RD0RC_1LE1LA_0LE0RB_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm738: ~halts (TM_from_str "1RB1RA_1LC1LF_1LE0LD_1RE0LC_0RA0RE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm739: ~halts (TM_from_str "1RB---_0RC1LF_1RD1RC_1LE1LD_0RB0LE_1LA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm740: ~halts (TM_from_str "1RB0RE_1RC1LA_1LD1LC_0RE0LD_0RF0LF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm741: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1RE_0RE0LD_0RF1RA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm742: ~halts (TM_from_str "1RB1LA_0RC1RC_1RD1RC_1RE0LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm743: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LB_1LC1RE_1RD0LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm744: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE1LE_0RF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm745: ~halts (TM_from_str "1RB1LC_1LB1RA_1LF0LD_1RE0LC_0RA1RB_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm746: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LE---_0LF1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm747: ~halts (TM_from_str "1RB0RC_0RC---_0RD0LF_1LE1RD_0LF0LC_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm748: ~halts (TM_from_str "1RB---_1RC1LE_1LD---_0RD0RB_0LF0LE_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm749: ~halts (TM_from_str "1RB---_1LC1RF_1RD1LD_0RE0LD_0RF0RC_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm750: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LB---_0LF1LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm751: ~halts (TM_from_str "1RB0RC_0LB1RC_0LD0LE_1RA1LD_0RA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm752: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1LC_1LA1LD_1RF1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm753: ~halts (TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_0RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm754: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LE---_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm755: ~halts (TM_from_str "1RB---_1LC1LF_0RA0LD_0RE0RF_1RE1RA_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm756: ~halts (TM_from_str "1RB---_1RC1RB_1RD1LA_1RE1LD_1LF0RC_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm757: ~halts (TM_from_str "1RB1LB_1RC1LF_1RD1RA_1LE0RA_0RB0LE_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm758: ~halts (TM_from_str "1RB---_1LC0LB_---0RD_1LF1RE_1RD1LB_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm759: ~halts (TM_from_str "1RB0LB_1LC0LF_---0RD_1LA1RE_1RD1LF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm760: ~halts (TM_from_str "1RB1RA_1RC---_1LD1LC_1RA1LE_0RF0LE_0RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm761: ~halts (TM_from_str "1RB0LF_0RC0RE_1LD0LA_0LE---_1LC1RE_0RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm762: ~halts (TM_from_str "1RB0LC_1LA1RB_1RD0LE_1RB0RB_1RF1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm763: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA0RE_0RD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm764: ~halts (TM_from_str "1RB0RE_1LC1RB_---0LD_1RA1LD_0LB0RF_0LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm765: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA1RD_0RF1LE_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm766: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0RD_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm767: ~halts (TM_from_str "1RB---_1RC1LD_1LB1LC_1LF0RE_1RD1RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm768: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD1LA_1RE0RB_---0LA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm769: ~halts (TM_from_str "1RB1RA_1RC1RA_1LC1LD_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm770: ~halts (TM_from_str "1RB1LF_1LC---_1RA1RD_0RD0RE_0RB0LE_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm771: ~halts (TM_from_str "1RB0LA_1LC1RE_---0LD_0RA0LF_1RA1LF_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm772: ~halts (TM_from_str "1RB0LF_1LC---_0RD0LC_0RE1RE_1RA1RD_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm773: ~halts (TM_from_str "1RB1LC_1RC1RB_1LD1LA_0RE0LD_1RF---_0RA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm774: ~halts (TM_from_str "1RB0RB_1LC1RB_1LB0LD_1RC0LE_1RF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm775: ~halts (TM_from_str "1RB1RA_1RC1LA_0LD0RC_0LB1LE_1LF1LD_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm776: ~halts (TM_from_str "1RB1RC_1LA1LD_0RC0RB_0LF0LE_0LA1RE_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm777: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD0RE_1LA---_1RE0RF_1LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm778: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RB_0LD1RA_1LE0RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm779: ~halts (TM_from_str "1RB0RB_1RC1LB_1RD1RA_1LE1RF_0RD0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm780: ~halts (TM_from_str "1RB0LF_0RC---_1RD1LE_1RE1RD_1LF1LC_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm781: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA0LA_1LD0RF_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm782: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA0RE_0LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm783: ~halts (TM_from_str "1RB0LC_1RC1RA_1RD1LA_1LE1RF_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm784: ~halts (TM_from_str "1RB1RD_1LC0LF_---0RA_1RE1LF_1LF1RD_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm785: ~halts (TM_from_str "1RB0LB_1LA0RC_0RD---_1RE1RD_1LF1LE_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm786: ~halts (TM_from_str "1RB1LC_1LB1RA_0LD0RA_0RA0LE_---0LF_0RC0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm787: ~halts (TM_from_str "1RB1LE_1LC1RD_1RD1LC_---0LA_1LA1RF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm788: ~halts (TM_from_str "1RB1RA_0LC0RE_1LF1LD_1LA1LC_0LF0RB_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm789: ~halts (TM_from_str "1RB1RC_0RC0LD_1LD0RE_1LD0LA_1LF1RE_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm790: ~halts (TM_from_str "1RB1RA_1RC0RC_1LD1RE_---1LE_1LA0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm791: ~halts (TM_from_str "1RB1RA_0LC0RB_0LD1LB_1LE---_1LF1LE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm792: ~halts (TM_from_str "1RB1LD_1RC---_1LD0LD_0RF0LE_0LC0RC_1RF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm793: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1RD_1LF1LE_1LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm794: ~halts (TM_from_str "1RB0RC_0RC0LD_1LD0RE_0LA0LF_1LB1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm795: ~halts (TM_from_str "1RB0LA_1RC0LC_1LD1LB_---0RE_1LA1RF_1RE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm796: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LE---_0LF1LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm797: ~halts (TM_from_str "1RB0RF_1LC1RB_---0LD_1RA0LE_1RA1LE_1RB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm798: ~halts (TM_from_str "1RB1LB_1LC1RD_1LA0RA_1LE0RB_---0LF_1LE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm799: ~halts (TM_from_str "1RB1RA_0RC1LD_1LB1LC_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm800: ~halts (TM_from_str "1RB0RF_1LC0LF_0RD0LC_1RE---_0RA1RA_1LD1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm801: ~halts (TM_from_str "1RB0LA_0RC1RC_1RD1LA_1LE1LA_---0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm802: ~halts (TM_from_str "1RB0LB_0RC1LA_1RD---_1RE1RD_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm803: ~halts (TM_from_str "1RB---_1RC1LD_1LD0RC_1RF0LE_1LC0LD_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm804: ~halts (TM_from_str "1RB1LC_0LC1RC_1LE0RD_0LE0RC_1LF---_1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm805: ~halts (TM_from_str "1RB0LD_1RC1LD_1LD0RB_0LA0LE_0LF1RE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm806: ~halts (TM_from_str "1RB0LF_0RC1RA_1RD1RC_1LE1LD_---1LB_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm807: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE0LD_1LB0RD_0LB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm808: ~halts (TM_from_str "1RB---_0LC0RB_0LE1LD_1LB1LA_1LF1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm809: ~halts (TM_from_str "1RB1LF_1RC1LB_1RD1RA_1LE0RA_0RC0LE_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm810: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_---0RE_0LF0RF_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm811: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0RC_1LA1RE_1RF0RE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm812: ~halts (TM_from_str "1RB1LE_1RC1LA_0LC1LD_0RF0RB_0LA1RF_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm813: ~halts (TM_from_str "1RB1LF_1LC1RE_1LD0LD_0RB0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm814: ~halts (TM_from_str "1RB0LB_1LC1RF_0RD0LC_1RE---_0RA1RA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm815: ~halts (TM_from_str "1RB0RA_0LC0LE_0LD1LB_1RD1RA_---1LF_0RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm816: ~halts (TM_from_str "1RB1LA_0LC0RB_0LD1LB_1LE---_1LF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm817: ~halts (TM_from_str "1RB0LE_1RC1LE_1LD---_0RD0RB_0LF0LA_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm818: ~halts (TM_from_str "1RB1LC_1LA1RE_1LD0LE_1LB0RD_0LF0RE_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm819: ~halts (TM_from_str "1RB0RD_1LC0RB_0LE0LD_1RD1RB_0LF---_1LF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm820: ~halts (TM_from_str "1RB1RF_1RC1LE_1LD0RB_0RC0LD_1RA0LB_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm821: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LE1RB_0LF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm822: ~halts (TM_from_str "1RB1LD_0RC1LD_1LA1RE_---0RC_1RC1LF_0LB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm823: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RA_0RA0LD_1RC0LF_0LF1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm824: ~halts (TM_from_str "1RB1RA_1RC0LE_1LD---_0RE0LD_1LF1LE_1RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm825: ~halts (TM_from_str "1RB1LA_1RC1LF_1RD---_1LE0RF_0RB0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm826: ~halts (TM_from_str "1RB0LF_0RC1RE_0RD---_1LA1LD_1RD1RE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm827: ~halts (TM_from_str "1RB---_1RC1LE_1LC1RD_1RA1LE_0RA0LF_0LE0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm828: ~halts (TM_from_str "1RB0LE_1RC1LF_0RD0RB_1LE---_0LA1RA_0LB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm829: ~halts (TM_from_str "1RB1RD_0RC---_1RD1LC_1LE1RF_0RB0LE_1RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm830: ~halts (TM_from_str "1RB1RE_0RC1RA_1LD1LC_0RA0LD_1RC1RF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm831: ~halts (TM_from_str "1RB1LC_0LC0LE_---0RD_1LE1RF_1RA0LB_1RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm832: ~halts (TM_from_str "1RB1LC_1LC1RE_---0LD_0LE0LF_1RA0LC_0RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm833: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_1RC---_0LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm834: ~halts (TM_from_str "1RB---_1LC1RD_0LE0RD_1RA1LC_1RE0LF_0RD0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm835: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1LE1RF_0RF0LE_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm836: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LE0LE_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm837: ~halts (TM_from_str "1RB1LA_0RC1RC_1LD1RF_0LE---_0RA0LE_1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm838: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_1RC1RA_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm839: ~halts (TM_from_str "1RB1LA_0RC1LB_1RD1RC_1RE1LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm840: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD0LB_1RE0RB_---0LA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm841: ~halts (TM_from_str "1RB1RE_1LC---_0LE1LD_1LE1LC_0RA0RF_0LC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm842: ~halts (TM_from_str "1RB1RF_0LC0RD_1LE1LA_0LE0RB_0LA---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm843: ~halts (TM_from_str "1RB0LB_1LC0RD_1LA0LC_0RE---_1RF1RE_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm844: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_0RE1RC_1LF1RE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm845: ~halts (TM_from_str "1RB1RA_0LC0RB_1LF1LD_0RE---_1LA1LE_0LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm846: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm847: ~halts (TM_from_str "1RB1LA_1LA0RC_1RA0RD_1LE1RD_1LC0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm848: ~halts (TM_from_str "1RB1RA_1LC1LB_---1LD_0RA1RE_1RD0LF_0RD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm849: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_1RF0RE_0LB1LD_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm850: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1RE---_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm851: ~halts (TM_from_str "1RB---_0RC1LC_1LD0RB_1LE1RF_0LA0LD_0RD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm852: ~halts (TM_from_str "1RB0LA_1RC0LD_1LD1RF_---1LE_0LB0RC_0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm853: ~halts (TM_from_str "1RB---_1LC1RB_1LD1LC_1LE1LA_1RF0LD_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm854: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LC_1LE0LF_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm855: ~halts (TM_from_str "1RB0RC_0RC0LD_1LD0RE_0LA1LF_1LB1RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm856: ~halts (TM_from_str "1RB1LE_0RC1RB_1LD1RC_1RC0LE_---0LF_0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm857: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0LB_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm858: ~halts (TM_from_str "1RB1LA_1LC0RD_---1LA_0LF0RE_1LF1RE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm859: ~halts (TM_from_str "1RB0RA_1RC0RF_1LD1RB_---0LE_0LA1LE_0LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm860: ~halts (TM_from_str "1RB0LB_1RC1LB_1RD0RF_1RE0LA_1LD1RE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm861: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1RD_1LA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm862: ~halts (TM_from_str "1RB1RD_1RC1RF_0LD0RA_1RA0LE_0RB1LD_1LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm863: ~halts (TM_from_str "1RB1RF_0RC---_1LD1LC_1LE1RC_0RF0LE_0RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm864: ~halts (TM_from_str "1RB0LE_1LC0RC_0RF1RD_---1LA_0LB1LE_0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm865: ~halts (TM_from_str "1RB0LA_1RC---_0RD1RD_1RE1LF_1LC1LA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm866: ~halts (TM_from_str "1RB1LE_1RC---_0RD1LC_1RE1RD_1LF1LA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm867: ~halts (TM_from_str "1RB0LE_1RC1RF_0RD---_1LE1LA_1LB0LA_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm868: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LE_1LE1RA_0RD0LF_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm869: ~halts (TM_from_str "1RB1LF_1LC1LF_---0LD_0RE0LC_0RA1RA_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm870: ~halts (TM_from_str "1RB1LB_1RC1LD_0RD0RC_0RE1LA_1LF---_0LF0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm871: ~halts (TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm872: ~halts (TM_from_str "1RB---_0RC1RC_1RD0LD_1LE1RF_0RA0LE_1LC1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm873: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD0LE_---1LB_0RA0LF_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm874: ~halts (TM_from_str "1RB1RE_1RC---_1LD0RE_0RA0LD_1RA1LF_1RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm875: ~halts (TM_from_str "1RB---_1LC1LB_1LD1RC_1RF0LE_1LA1RA_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm876: ~halts (TM_from_str "1RB0LC_1LC0LE_1LA1RD_0RC0RB_0LF1RA_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm877: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB0LD_0LF0RC_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm878: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE1LA_1LA0RB_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm879: ~halts (TM_from_str "1RB1RE_0LC0RB_1LE1LD_0LE---_0LF1RA_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm880: ~halts (TM_from_str "1RB0RC_0RC---_0RD0LF_1LE1RD_1LB0LC_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm881: ~halts (TM_from_str "1RB1LF_0RC---_1RD0LC_1RE---_1LA1RC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm882: ~halts (TM_from_str "1RB0LD_1RC1LA_1LA1RA_0LF0LE_0RA1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm883: ~halts (TM_from_str "1RB1RA_1RC1RA_0LD0RC_0LB1LE_1LF1LD_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm884: ~halts (TM_from_str "1RB1RA_1LC0RB_1RC0RD_---1LE_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm885: ~halts (TM_from_str "1RB1RD_1RC---_0RD1RD_1RE1RA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm886: ~halts (TM_from_str "1RB---_0RC0LF_0RD1RE_1LB1LD_1RD1RE_1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm887: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_1RF1LD_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm888: ~halts (TM_from_str "1RB1LF_0RC1RE_0RD0LC_1LA---_1LA1RC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm889: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1RA0RF_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm890: ~halts (TM_from_str "1RB1LC_1LB1RA_0LE0LD_1RE0LC_1LF0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm891: ~halts (TM_from_str "1RB1RA_1LC0RB_0RC0LD_0LE1RE_1LF---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm892: ~halts (TM_from_str "1RB1RF_0RC0RA_1LD---_1LE1LF_0RA0LE_1RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm893: ~halts (TM_from_str "1RB---_1LC1LB_1LE1LD_0RE0LD_0RF1RE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm894: ~halts (TM_from_str "1RB1RD_0LC0LA_1LF1LA_0RE0RD_0LF0RB_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm895: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA0LF_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm896: ~halts (TM_from_str "1RB1LE_1LC1RA_1RD0LC_0RA0LE_1LF0LD_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm897: ~halts (TM_from_str "1RB1RA_1LC0RB_0LD1RC_0LA0LE_---1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm898: ~halts (TM_from_str "1RB1LF_1LC0RA_1RE1LD_1LE---_1RA0RC_0LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm899: ~halts (TM_from_str "1RB0LE_1RC1RA_1RD1RF_0LA0RB_0RC1LA_1LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm900: ~halts (TM_from_str "1RB1LC_1LC1RE_0LF0LD_0RA1RD_1RA0LC_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm901: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LF_1RF1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm902: ~halts (TM_from_str "1RB1LE_0RC1RF_1RD---_1LA1LD_0RB0LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm903: ~halts (TM_from_str "1RB1RA_1RC0RB_1LC0LD_1LF1LE_0LD---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm904: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1RA1RF_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm905: ~halts (TM_from_str "1RB1LA_0LC0RF_1LD1RC_---0LE_1RF0LA_1RC0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm906: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RA0RF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm907: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0RB_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm908: ~halts (TM_from_str "1RB0LE_1LC1LB_1RA0LD_1RE1LE_0RF1RC_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm909: ~halts (TM_from_str "1RB---_1LB1LC_1LD1RD_1LA0RE_0LB0RF_0RD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm910: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LF_1RA1RD_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm911: ~halts (TM_from_str "1RB1LC_1LC1RE_0LC0LD_0RA0RD_1RF1LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm912: ~halts (TM_from_str "1RB0LA_0RC1RD_1LA1LE_1LC1LD_---0RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm913: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LB_1LA1RD_1LD1LF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm914: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD0RF_1LE1LA_0RB0LE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm915: ~halts (TM_from_str "1RB1RC_0RC0LC_0RD0LA_1LE1RD_0LC0LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm916: ~halts (TM_from_str "1RB0LF_0RC---_1RD1LC_1LE1RF_0RB0LE_1RC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm917: ~halts (TM_from_str "1RB1LE_1LC1RD_0LE0LD_0LC0RD_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm918: ~halts (TM_from_str "1RB1LD_1LC1LF_0RE0RA_0LC0LD_1RF---_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm919: ~halts (TM_from_str "1RB1RE_1RC1RB_1LD1LC_0RE0LD_0RF0LF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm920: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD---_1LE1LA_0RB0LF_0RC0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm921: ~halts (TM_from_str "1RB0RB_1LC1RB_1RB0LD_0RB0LE_1RF1LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm922: ~halts (TM_from_str "1RB1LA_1LA1RC_1RF1RD_0RE0LF_0RC---_1RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm923: ~halts (TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_0LA0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm924: ~halts (TM_from_str "1RB0RD_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm925: ~halts (TM_from_str "1RB0LB_1LC0LF_---0RD_1LD1RE_1RD1LA_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm926: ~halts (TM_from_str "1RB1RE_0RC1LD_1LA1LF_0LF0LA_0RE0RB_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm927: ~halts (TM_from_str "1RB1RA_1RC0RB_1LC0LD_1LF0LE_0LF---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm928: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LC_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm929: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RA_0RB0LD_1LF1LA_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm930: ~halts (TM_from_str "1RB1RA_1RC0RB_1LC0LD_1RE0LE_0LF---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm931: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RE---_1RF1RA_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm932: ~halts (TM_from_str "1RB1LB_1RC0LF_1RD---_1RE0RE_1LA1RB_0RC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm933: ~halts (TM_from_str "1RB1LC_1LC0LD_0LC1LD_1RE0RB_0RF0RA_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm934: ~halts (TM_from_str "1RB0RE_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm935: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LE_1LE1RA_0LE0LF_0RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm936: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RD_1LA1LF_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm937: ~halts (TM_from_str "1RB1RF_1LC0RB_0LA1RD_---0LE_1LA1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm938: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1LA_1RE---_1LF0RB_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm939: ~halts (TM_from_str "1RB---_1RC1RB_1RD1LC_1LE0RF_0RD0LE_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm940: ~halts (TM_from_str "1RB1LD_0RC1RA_1LD1LA_0LE0RA_---0LF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm941: ~halts (TM_from_str "1RB1RA_1RC1RD_1LD0RC_1LF0LE_1LB1LE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm942: ~halts (TM_from_str "1RB0LE_0RC1RD_1LA1RB_0LA1RB_---1LF_0LD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm943: ~halts (TM_from_str "1RB---_0RC0RB_1RD1LE_1LD1RC_0LF0LB_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm944: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA1RB_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm945: ~halts (TM_from_str "1RB1RC_0RC0RE_1LD1LF_0RA0LD_1LB---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm946: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_1RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm947: ~halts (TM_from_str "1RB1RE_1RC0RA_1LC1LD_0RA0LD_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm948: ~halts (TM_from_str "1RB1RE_0RC---_1LD1LC_0RA0LF_1RC1RA_0RC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm949: ~halts (TM_from_str "1RB0LF_0RC0RD_1LD0LA_1LE1RD_---0LA_0RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm950: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA1RB_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm951: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RA_0RB0LD_1RF0LE_1RF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm952: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RF1LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm953: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_1RC1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm954: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LA1RE_1LF0RD_1LD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm955: ~halts (TM_from_str "1RB0LE_0RC0RB_1RD1LF_1LE1RC_---0LB_0LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm956: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1LC---_1RF1RA_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm957: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LF_0LA1LC_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm958: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LF0RE_0LA1RB_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm959: ~halts (TM_from_str "1RB0RD_1RC---_0LA1LA_0RE0LC_1LF1RE_0LC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm960: ~halts (TM_from_str "1RB1LE_1RC1RD_1LD0LD_---0LA_1LA1RF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm961: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA0RE_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm962: ~halts (TM_from_str "1RB1RA_1RC0LF_1LD0RE_0RC0LD_1RA---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm963: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE0LD_1LA0RB_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm964: ~halts (TM_from_str "1RB1RA_1LC1LF_1LD0LC_1RE0LE_0RA0RE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm965: ~halts (TM_from_str "1RB1RC_0RC0RB_1LD1LE_0LA1RB_0LF---_0LE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm966: ~halts (TM_from_str "1RB0LD_0RC0RE_1LD0RB_1LA1RB_0RF0LB_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm967: ~halts (TM_from_str "1RB1RF_1LC0LF_0RD0LC_1RE---_0RA1RA_1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm968: ~halts (TM_from_str "1RB1RE_0RC1LF_1LD1LC_0RA0LD_1RC1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm969: ~halts (TM_from_str "1RB1LF_1LC1RD_0RB0LC_0RE1RA_0RA---_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm970: ~halts (TM_from_str "1RB1LF_1LC0RE_1RD0LC_0RE---_1RA1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm971: ~halts (TM_from_str "1RB1LD_1RC1RB_1RD---_1RE1LA_1LF0RB_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm972: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0RE_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm973: ~halts (TM_from_str "1RB1LF_1LC1RA_---1LD_1RE0RE_0LC0RA_0LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm974: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RD_1LA1LF_1LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm975: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE1LB_1LB0RD_0LB1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm976: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE1LD_1LF---_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm977: ~halts (TM_from_str "1RB1LE_1RC---_1RD0RD_0LE0LA_0RC1LF_1LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm978: ~halts (TM_from_str "1RB1RC_1LA1LE_0RF0RD_0RB0LD_0LA0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm979: ~halts (TM_from_str "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm980: ~halts (TM_from_str "1RB0RE_1LC1LD_0RB1LB_0RA0LB_0LA1RF_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm981: ~halts (TM_from_str "1RB1RF_0RC---_1RD1LA_1RE1RD_1LC1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm982: ~halts (TM_from_str "1RB---_1LC1RF_0RB0LD_0LE0RB_1RE0LC_1RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm983: ~halts (TM_from_str "1RB0RD_1LC0RA_1RB1LC_1LE1RD_0LC0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm984: ~halts (TM_from_str "1RB0LC_1RC1RA_1RD1LA_1LE0RF_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm985: ~halts (TM_from_str "1RB0LE_0RC0LA_1RD1RC_1LB1LD_0LF0LA_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm986: ~halts (TM_from_str "1RB1RF_1RC1LF_1LD0RD_0RE0LD_0RB---_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm987: ~halts (TM_from_str "1RB---_0RC1LC_1RD1RC_1LE1LF_0RB0LE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm988: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1RD_1LF1LE_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm989: ~halts (TM_from_str "1RB0LF_1LC1RD_0RD0LC_0RE---_1RA1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm990: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LA1RE_1LF0RD_1LD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm991: ~halts (TM_from_str "1RB1LA_1LA0RC_0RF0RD_1LE1RD_1LC0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm992: ~halts (TM_from_str "1RB---_0RC---_1RD1RC_1LE1LD_1LB0LF_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm993: ~halts (TM_from_str "1RB1LF_1LC0RB_1LD0RC_1RE0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm994: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA0RE_0RD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm995: ~halts (TM_from_str "1RB1RE_1RC0LE_1LD0RB_0RC0LD_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm996: ~halts (TM_from_str "1RB1LA_0RC1LC_1RD1RC_1RE1LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm997: ~halts (TM_from_str "1RB0LD_0RC0RE_1LD0RB_1LA1RB_1RF0LB_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm998: ~halts (TM_from_str "1RB1LA_1RC1RF_0RD---_1LE1LA_0RB0LE_1RD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm999: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_1RC1RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1000: ~halts (TM_from_str "1RB1RC_1LC0RB_0LF1RD_---0LE_1LF1LE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1001: ~halts (TM_from_str "1RB1RA_1LC1LB_1LD0LC_1RE0LE_---0RF_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1002: ~halts (TM_from_str "1RB0LF_0RC---_1RD1RC_1LE1LD_1LA0LF_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1003: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD0LA_1RE---_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1004: ~halts (TM_from_str "1RB1RC_0LC0RB_1RD1RC_1LE1RE_---0LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1005: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD---_0RB0LD_1RF1RE_1RC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1006: ~halts (TM_from_str "1RB1LF_1LC0RC_1RE0LD_0RB0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1007: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE1LF_1LC1RE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1008: ~halts (TM_from_str "1RB---_1LC0LF_1LE1RD_0RC0RB_1RF0LC_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1009: ~halts (TM_from_str "1RB1RF_1RC1LA_1RD1LC_1LE0RB_0RD0LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1010: ~halts (TM_from_str "1RB1RA_1LC0RD_0RD0LC_0RE---_1RF1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1011: ~halts (TM_from_str "1RB0LA_0RC1LD_1LA1LB_---0RE_1RF1RE_1RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1012: ~halts (TM_from_str "1RB1RC_0RC1LA_1RD1RC_1LE1LF_0RB0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1013: ~halts (TM_from_str "1RB1RE_1LC0RB_0LA1LD_1RA1RD_---0LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1014: ~halts (TM_from_str "1RB1LE_0RC0LB_0RD---_1RE1RD_1LF1LA_1LC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1015: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1RE1RA_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1016: ~halts (TM_from_str "1RB1LF_1LC1RE_1RE0LD_0RB0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1017: ~halts (TM_from_str "1RB---_1RC1LB_1RD1LF_1LE0RA_0RC0LE_1RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1018: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1019: ~halts (TM_from_str "1RB1LA_0RC1RF_1RD0LE_1LE---_0RA0LC_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1020: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RE1LD_1RF1RE_1RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1021: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA1RB_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1022: ~halts (TM_from_str "1RB---_0RC0LB_1RD0RF_1LE1LD_1LA1LB_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1023: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LA0RE_1LF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1024: ~halts (TM_from_str "1RB1LB_0RC0LB_0RD---_1RE0LD_1RF---_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1025: ~halts (TM_from_str "1RB1RF_0LC0RB_1LE1LD_1LA1LC_0LD1RD_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1026: ~halts (TM_from_str "1RB0LF_1LC---_0RD0LC_0RE1RE_1RA1RD_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1027: ~halts (TM_from_str "1RB1LA_1RC1RB_0RD1LA_1LD1RE_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1028: ~halts (TM_from_str "1RB0RB_1LC1RB_1RA0LD_0RA0LE_1RC1LF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1029: ~halts (TM_from_str "1RB0RF_1RC0LD_1LB1RC_---0LE_1RA1LE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1030: ~halts (TM_from_str "1RB1RA_1RC0RA_1LD1LF_1RA1LE_0RB0LE_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1031: ~halts (TM_from_str "1RB1LE_1LC1RA_0RA0LD_1RC0LC_0LF0LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1032: ~halts (TM_from_str "1RB1RF_0LC0RD_1LA1LC_0LA0LE_0RB0RF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1033: ~halts (TM_from_str "1RB1LD_1LC1LF_0RE0RA_0LC0LF_1RE1RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1034: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD---_0RB0LD_1RF1RE_1RC1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1035: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA0RE_0LD1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1036: ~halts (TM_from_str "1RB0LD_0LC0RB_1LF1LD_1LE1LD_1LC1RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1037: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE0LE_1RF1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1038: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1039: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE---_1RA1RE_1RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1040: ~halts (TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC1LE_---1LC_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1041: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_0RE1RE_0LF0RC_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1042: ~halts (TM_from_str "1RB0RE_1LC1LF_1LD0LC_0RA1RA_1RD---_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1043: ~halts (TM_from_str "1RB1RF_1LC0RD_0RA0LC_1RE---_1RA1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1044: ~halts (TM_from_str "1RB1RA_0RC0RB_1LD0LC_0LE---_1LF1LD_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1045: ~halts (TM_from_str "1RB1RA_1LC1RE_1LD1LC_1LA0LC_0LF0RE_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1046: ~halts (TM_from_str "1RB0LA_0RC1RE_1LD1LA_0RB0LF_1RC1LA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1047: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD1RD_1RE0RB_---0LA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1048: ~halts (TM_from_str "1RB1LA_1LC1RE_0RD0LC_0RE1RE_1RF1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1049: ~halts (TM_from_str "1RB0LD_1LC0RD_0RB0LC_1RE1LD_1RF1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1050: ~halts (TM_from_str "1RB---_0RC0LE_1RD1LF_1RE0LD_1LC1RD_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1051: ~halts (TM_from_str "1RB0LE_0RC---_1RD1RC_1LA1LF_0RB0LA_1RD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1052: ~halts (TM_from_str "1RB1LD_0RC1RF_0LD---_1LE0RD_1LA0LC_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1053: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_1RF1RE_0LF1RB_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1054: ~halts (TM_from_str "1RB1LC_0RC0LB_0RD---_1RE1RD_1RF1LE_1LB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1055: ~halts (TM_from_str "1RB0RC_1LC1LF_---1LD_0RE0LD_1RA1RF_1RE0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1056: ~halts (TM_from_str "1RB1LE_1LC0RB_0LE0RD_0RF0RC_1LA1RD_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1057: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB0LD_0RE0RF_1RD---_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1058: ~halts (TM_from_str "1RB0RE_1RC1LB_1RD0RA_1RE0LF_1LD1RE_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1059: ~halts (TM_from_str "1RB1RF_1LC0RD_0RA0LC_1RE0LB_1RA1LE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1060: ~halts (TM_from_str "1RB---_1RC0RE_1LD0RE_1LA0RD_0RC1LF_0LF0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1061: ~halts (TM_from_str "1RB---_0RC0LB_0RD1RE_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1062: ~halts (TM_from_str "1RB0LA_0RC1LB_0RD1RA_1LE1RD_0LC0LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1063: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LB_1LE0LF_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1064: ~halts (TM_from_str "1RB0LF_0RC1LB_0RD0RE_1LA1LD_1RD1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1065: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LA_0LA1LE_1LA---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1066: ~halts (TM_from_str "1RB0LA_0LC0RB_1LA1LD_1LE0LF_1LC1RE_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1067: ~halts (TM_from_str "1RB1LA_0RC1RC_1LD1RF_0LE---_0RA0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1068: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1069: ~halts (TM_from_str "1RB1RA_1RC1LA_1RD1LF_1LE0RB_0RD0LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1070: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LC_0LA1LF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1071: ~halts (TM_from_str "1RB1LF_1LC1LE_0RD0LC_0RB1RA_1RD0LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1072: ~halts (TM_from_str "1RB1LA_0RC1RC_1RD1RC_1RE1LA_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1073: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LB---_0LF1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1074: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_---0RE_0LF0RF_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1075: ~halts (TM_from_str "1RB1LF_0RC1LB_1LA0RD_---1RE_0LA1RC_0LB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1076: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LF_1LE0RC_0RD0LE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1077: ~halts (TM_from_str "1RB1RF_0LC0RD_1LC1LA_0LE0LA_0RB0RF_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1078: ~halts (TM_from_str "1RB1RF_1RC0RA_1LD1LF_---1LE_0RA0LE_1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1079: ~halts (TM_from_str "1RB1LE_0LB1RC_0LD0RC_0LE1LD_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1080: ~halts (TM_from_str "1RB0RF_1LC1LD_1RF0LD_1LE0LC_0RA1RA_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1081: ~halts (TM_from_str "1RB0LE_1RC1RA_1RD0RF_1LA0RB_0RC1LA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1082: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1RE_1LA1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1083: ~halts (TM_from_str "1RB1LD_0RC---_1RD1RC_1LE1LA_1LB0LF_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1084: ~halts (TM_from_str "1RB1LF_1LC1LD_0RE0RB_0LC0LF_1RE1RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1085: ~halts (TM_from_str "1RB0LC_0RC0LF_0RD---_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1086: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1RA0RF_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1087: ~halts (TM_from_str "1RB0LC_1RC1RA_1RD1LA_1LE1RE_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1088: ~halts (TM_from_str "1RB0LA_1RC---_1LD1LC_1LA0RE_1RF1RE_1RD1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1089: ~halts (TM_from_str "1RB1LA_0RC0RC_1LD0RE_1LA0LA_1LF1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1090: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LE1LD_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1091: ~halts (TM_from_str "1RB1LF_0LC0RB_1LD1RC_0LE1LE_1LA1LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1092: ~halts (TM_from_str "1RB1LE_1LC0RA_1RA0RD_0RF1LB_0LA0LC_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1093: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1RA1RF_0RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1094: ~halts (TM_from_str "1RB1RA_1LC1LE_0RA0LD_0RB0RA_---0LF_0LC0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1095: ~halts (TM_from_str "1RB1LD_0LC1LD_1RE0LD_1LC0RB_0RF0RA_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1096: ~halts (TM_from_str "1RB1RD_1LC---_0LF1RA_1LE0RD_0LB0LA_1LF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1097: ~halts (TM_from_str "1RB0RF_0LC1LC_1LE1LD_1LB---_1RA1RF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1098: ~halts (TM_from_str "1RB1RA_0LC0RB_1RE1LD_0LE---_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1099: ~halts (TM_from_str "1RB---_0RC1RC_1LD1LF_0RB0LE_0RA0LD_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1100: ~halts (TM_from_str "1RB---_1LC1LB_1RF1LD_0RE0LD_0RC1RF_1RA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1101: ~halts (TM_from_str "1RB1LC_1LC1RA_1LF0LD_1RE0LC_0RA1RB_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1102: ~halts (TM_from_str "1RB0LD_1LC1RE_0LA1RC_1LF1LA_0RC0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1103: ~halts (TM_from_str "1RB1RA_1LC1LB_0LE0LD_0RE0LD_0RF---_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1104: ~halts (TM_from_str "1RB1RE_0RC---_1LD1LC_0RA0LF_1RC1RA_0RB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1105: ~halts (TM_from_str "1RB1RA_1LB0LC_1LD1LC_1LE1RA_1RF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1106: ~halts (TM_from_str "1RB1LB_0RC0LB_0RD---_1RE1RD_1LF1LE_1LC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1107: ~halts (TM_from_str "1RB0RE_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1108: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1109: ~halts (TM_from_str "1RB0LE_1LC0RF_1RD0LC_0RA---_1LB1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1110: ~halts (TM_from_str "1RB0LA_1LC0RB_1LF1RD_---0RE_1LA1RE_1LB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1111: ~halts (TM_from_str "1RB0LA_0RC1LB_0RD0RE_1LA1LD_---1RF_1RD1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1112: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LC_0LE1RE_1LA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1113: ~halts (TM_from_str "1RB0LA_0RC---_1RD0LE_1LA0RF_1LD1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1114: ~halts (TM_from_str "1RB1LF_0RC1LA_1RD1RC_1LE1LD_0RB0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1115: ~halts (TM_from_str "1RB0RB_1RC0RC_1LD1RC_1RC0LE_---0LF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1116: ~halts (TM_from_str "1RB1RD_1RC0RF_1LD---_0LE1RA_1LA1LE_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1117: ~halts (TM_from_str "1RB1RF_0LC0RB_1LE1LD_1LA1LC_0LD1LD_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1118: ~halts (TM_from_str "1RB1RE_0LC0RB_1LE1LD_0LB---_0LF1RA_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1119: ~halts (TM_from_str "1RB1RF_1RC---_1LD0RE_0RA0LD_1RA1LE_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1120: ~halts (TM_from_str "1RB---_0RC0RB_1LD0RE_0LD1RA_0RF---_1LF1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1121: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD1LC_0RE0LD_1RF---_0RB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1122: ~halts (TM_from_str "1RB0RB_1RC1LB_1RD1RA_1LE1RF_0RD0LE_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1123: ~halts (TM_from_str "1RB1LE_1LC0RD_0RB0LC_1RA1RD_---1LF_1RD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1124: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE1RE_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1125: ~halts (TM_from_str "1RB0LF_0RC1LA_1RD0LC_1RE---_1LB1RC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1126: ~halts (TM_from_str "1RB1LC_1LB1RA_0LE1LD_1RE0RF_---0RA_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1127: ~halts (TM_from_str "1RB0LE_0LC0RA_1RE0LD_0RB1LF_1RA0LB_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1128: ~halts (TM_from_str "1RB1LE_1LC0RB_1LF1RD_---0LA_1LA1RF_0RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1129: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LC_0RE0LD_1RF---_0RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1130: ~halts (TM_from_str "1RB1RF_0LC0RB_0LD1LC_1LE---_1LA1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1131: ~halts (TM_from_str "1RB1LC_1LB1RA_---0LD_0RE0LE_0LF0RE_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1132: ~halts (TM_from_str "1RB0LE_1RC---_1LD0RA_0RB0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1133: ~halts (TM_from_str "1RB0RD_1LB1LC_0RD0LC_1RA1RE_1RD0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1134: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB1RE_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1135: ~halts (TM_from_str "1RB0LA_1RC---_1LD1LC_1LA0RE_1RF1RE_1RD0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1136: ~halts (TM_from_str "1RB1RE_1LC1LB_0RD0LC_1RE---_0RF1RA_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1137: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1138: ~halts (TM_from_str "1RB0RB_1RC1LD_1LA---_0LE0LD_1RA1RF_0RF0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1139: ~halts (TM_from_str "1RB1LE_0RC0LE_1LC0RD_---0LE_1LA1RF_1RC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1140: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1RE0LA_1RF0RF_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1141: ~halts (TM_from_str "1RB1RF_0LC0RE_0LA1LD_1LA1RF_---0RB_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1142: ~halts (TM_from_str "1RB1LF_1LC0LD_0LF1LD_1RE0RB_0RE0RA_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1143: ~halts (TM_from_str "1RB1LC_1LC1RE_0LE0LD_0RA1RD_1RA0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1144: ~halts (TM_from_str "1RB1LD_1LC0RB_1LE1LD_1LA1RE_1RF0RE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1145: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_0RA0LE_0RA0LF_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1146: ~halts (TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RE0LD_0RF0LF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1147: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE1RD_1RA1LB_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1148: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA0LC_---0RE_1RF1LC_1LD1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1149: ~halts (TM_from_str "1RB1LB_1LC0RD_1LF0LD_0LE0RB_0LB---_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1150: ~halts (TM_from_str "1RB1LF_1LC0RB_1LD1LA_1RE0RD_---0LA_0RE1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1151: ~halts (TM_from_str "1RB1LD_1LC1RF_0LD0LC_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1152: ~halts (TM_from_str "1RB1RE_1RC1RE_1LD0RC_0RA0LD_1RA1LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1153: ~halts (TM_from_str "1RB1LF_1LC0RB_1LD1LA_1RE0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1154: ~halts (TM_from_str "1RB1RE_1RC1LF_1LD1RF_0RE0LD_0RF---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1155: ~halts (TM_from_str "1RB1LC_0LA1RC_1LD0RF_1LE---_1LA0LA_0LD0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1156: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1LA_1RE---_1LF0RA_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1157: ~halts (TM_from_str "1RB1RF_1LC1LB_0RD0LC_1RE---_0RA1LE_1RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1158: ~halts (TM_from_str "1RB1LC_1LA1RC_0LD0LA_1LE0RE_0RF0LA_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1159: ~halts (TM_from_str "1RB0LE_0RC1LB_1RD1RC_1LA1LF_0RB0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1160: ~halts (TM_from_str "1RB1LE_0RC0LE_1LD1RA_0RA0LD_0LD0LF_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1161: ~halts (TM_from_str "1RB0LE_1RC1LE_1LD1RD_0RC1RB_0RC1LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1162: ~halts (TM_from_str "1RB0RB_1LC1RB_---0LD_1RE0LF_1LB0RA_1RE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1163: ~halts (TM_from_str "1RB0RB_0RC1LF_1LD1LF_0LE---_0LD1RA_0LF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1164: ~halts (TM_from_str "1RB1RE_1RC0LA_1LD1LC_0RE0LD_1RF---_0RB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1165: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA1RB_0LD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1166: ~halts (TM_from_str "1RB---_0RC1LF_1RD1LC_1LE1LD_0RA0LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1167: ~halts (TM_from_str "1RB0RA_1LC1RB_0RD0LD_1RA0LE_0LF1LD_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1168: ~halts (TM_from_str "1RB1LD_0LC1RE_1LD1LB_1LA1RF_---0LA_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1169: ~halts (TM_from_str "1RB1LA_1LC1LE_0RD0LC_0RE1RE_1RF1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1170: ~halts (TM_from_str "1RB1RC_1LA1LD_0RB0RC_0LF0LE_0LA0RE_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1171: ~halts (TM_from_str "1RB0RE_1LC1RB_---0LD_1RE0LF_1RB0RB_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1172: ~halts (TM_from_str "1RB1LB_1LC0LC_1LA1RD_0RE0RD_0LC1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1173: ~halts (TM_from_str "1RB1LC_0LA0RE_1LD1RB_1LA---_0RF0LE_0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1174: ~halts (TM_from_str "1RB0LE_1RC1LE_1LD0RB_0LF1RB_0LA0LD_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1175: ~halts (TM_from_str "1RB1LF_1RC0LF_1RD0LA_1LE0RB_0RC0LE_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1176: ~halts (TM_from_str "1RB---_1LC1RE_0RE1LD_0RB0LD_1RF0RF_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1177: ~halts (TM_from_str "1RB1LC_0LC0RB_0LE1LD_1LE1RA_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1178: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA1RB_0LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1179: ~halts (TM_from_str "1RB1LF_1LC1RA_0LE1LD_1RE0RE_---0RA_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1180: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE0LE_1RF1RC_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1181: ~halts (TM_from_str "1RB1RD_1LC0RD_0RB0LC_1RA1LE_0LF0LD_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1182: ~halts (TM_from_str "1RB1LD_1RC1RA_1LB1RA_0LE0RA_---0LF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1183: ~halts (TM_from_str "1RB1RF_1RC1LE_1LD0RB_0RC0LD_1RF1LB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1184: ~halts (TM_from_str "1RB1RF_1LC0RB_1LE0LD_0LB---_1RA1LB_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1185: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE0RF_1LF1LD_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1186: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LE_1RE0LD_0RA1LF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1187: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD0RE_1LA1LD_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1188: ~halts (TM_from_str "1RB1LC_1LC1RA_0LD0RA_0RA0LE_---0LF_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1189: ~halts (TM_from_str "1RB0LE_0RC0RB_1RD1RC_1LE1LF_1LB0LA_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1190: ~halts (TM_from_str "1RB1RA_1LC1LB_1LF1LD_1RE0LD_0RB0RA_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1191: ~halts (TM_from_str "1RB0RE_0RC0LB_1LD1RE_0RA1LB_1RF0LE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1192: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC0LA_0RB0LE_1LF1LA_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1193: ~halts (TM_from_str "1RB0LB_1LC0LF_---0RD_1LF1RE_1RD1LA_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1194: ~halts (TM_from_str "1RB1RF_1LC1LE_0RD0LC_1RE---_0RA1LB_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1195: ~halts (TM_from_str "1RB1RA_1RC1LA_1RD---_1RE1LD_1LF0RB_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1196: ~halts (TM_from_str "1RB0RB_0LC0RF_1LC1LD_1LE1RB_1LA---_0RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1197: ~halts (TM_from_str "1RB0LF_1LC0LB_---0RD_1LA1RE_1RD1LB_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1198: ~halts (TM_from_str "1RB1RD_0RC0LB_0RD1LD_1RE---_1RF0LA_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1199: ~halts (TM_from_str "1RB1RE_0LC0RD_1LF1LA_0LE0RB_1LC0RE_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1200: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1LC_1LA1LD_1RF1RE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1201: ~halts (TM_from_str "1RB0LB_0RC1LB_1LD0RE_1LA---_0LD1RF_0RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1202: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LE1LA_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1203: ~halts (TM_from_str "1RB0LA_1RC---_0RD1RD_1LE1LA_0RC0LF_0RB0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1204: ~halts (TM_from_str "1RB0LE_1RC---_1LD0RE_0RB0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1205: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_0LE1LE_0RF0LB_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1206: ~halts (TM_from_str "1RB1LD_1RC1RF_0RD---_1LE1LA_0RB0LE_1RD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1207: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0RE---_0LA1LF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1208: ~halts (TM_from_str "1RB1LC_1RC1RB_1RD1LA_1RE---_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1209: ~halts (TM_from_str "1RB---_1RC1LB_1LD1RE_0RE0LD_0RC1RF_1RA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1210: ~halts (TM_from_str "1RB1RC_0LC0LE_0RA0LD_1RE0LF_1RA0RB_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1211: ~halts (TM_from_str "1RB1RD_1LC0LC_1RA1LD_1LE0RF_1LB---_0LE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1212: ~halts (TM_from_str "1RB1RF_1LC0RF_1LD0LD_0LE1LE_1LA---_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1213: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RC_0RB0LD_1RA0RF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1214: ~halts (TM_from_str "1RB---_0RC0LC_0RD0LC_1RE1RD_1LF1LE_1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1215: ~halts (TM_from_str "1RB1LE_0RC1LF_1LD---_1RA1RE_0RE0RB_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1216: ~halts (TM_from_str "1RB0LA_0RC---_1RD1RC_1RE1LF_1LA0RC_1LE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1217: ~halts (TM_from_str "1RB0LA_0LC0RB_1LF1LD_1LE1LD_1LC1RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1218: ~halts (TM_from_str "1RB1LC_1LA0RF_1LD---_0RE0LD_1LB0LB_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1219: ~halts (TM_from_str "1RB0LE_1LC0RD_0RD0LC_0RE---_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1220: ~halts (TM_from_str "1RB1LE_0LC0RB_1LD1RD_0LE---_1LF1RF_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1221: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0LA0LC_---0RF_0RB0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1222: ~halts (TM_from_str "1RB1LF_1LC0RA_1RC0LD_0LC0RE_1RA---_0LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1223: ~halts (TM_from_str "1RB0LC_1LA1RB_0LD0LD_1RE1LD_1RA0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1224: ~halts (TM_from_str "1RB0LD_1RC1RA_1LB1RE_0RE1LA_1LD1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1225: ~halts (TM_from_str "1RB0LF_0RC1RD_1RD---_1RE1RD_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1226: ~halts (TM_from_str "1RB0LB_1LC1LA_---0RD_1LF1RE_1RD0RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1227: ~halts (TM_from_str "1RB1LE_1LC0RD_0RA0LC_1RA1LD_1RD1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1228: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_1LF1LE_0RF0LB_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1229: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE0RA_1RF0LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1230: ~halts (TM_from_str "1RB1LF_1LC0RD_0RB0LC_1RE1RD_1RA---_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1231: ~halts (TM_from_str "1RB0RE_1LC1RE_1LA1LD_1LC0LB_0RF0RC_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1232: ~halts (TM_from_str "1RB0LE_0RC---_1RD1RC_1LE1LD_0LF0LA_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1233: ~halts (TM_from_str "1RB0RB_0RC---_1RD1RC_1LE1LD_1LF0LE_1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1234: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LE1RE_0LF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1235: ~halts (TM_from_str "1RB1LC_0LC0RE_1LD1RD_1LA0RD_---1RF_0LF1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1236: ~halts (TM_from_str "1RB0LD_1RC1LB_1RD1RF_1LE0RA_0RC0LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1237: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE0RF_1LF1LD_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1238: ~halts (TM_from_str "1RB0LD_0RC0RF_1LC0LA_0RE1LD_---1RB_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1239: ~halts (TM_from_str "1RB0LA_1RC1RF_1LD0LC_---0RE_1LA0RE_1RE1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1240: ~halts (TM_from_str "1RB0RE_0RC0LD_1LD0RF_0LA1LB_0LB1RC_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1241: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1242: ~halts (TM_from_str "1RB1LF_1LC1LE_---0LD_0RE0LC_0RA1RA_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1243: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LC_1LF1LB_1RD1RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1244: ~halts (TM_from_str "1RB---_1RC1RA_0RD0RF_1LE0RB_1LC0LD_0LD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1245: ~halts (TM_from_str "1RB---_1RC1RB_0LD0RC_0LB1LE_1LF1LD_1LB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1246: ~halts (TM_from_str "1RB---_0RC1LE_0RD1RC_1LA1LF_0RB0LE_1LD0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1247: ~halts (TM_from_str "1RB1LE_1LC0RD_0RA0LC_1RA1LD_1RF1RE_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1248: ~halts (TM_from_str "1RB0LE_1RC1RA_1RD1RF_1LA0RB_0RC1LA_1LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1249: ~halts (TM_from_str "1RB1LA_1LA0RC_0LE0RD_1LE1RD_0LA0LF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1250: ~halts (TM_from_str "1RB0LC_1LA---_0RD0LF_1RD1RE_1RA1LA_0LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1251: ~halts (TM_from_str "1RB0LD_0RC1LA_1LA0RB_0LE1RE_0LF---_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1252: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_0RA0LE_0RF0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1253: ~halts (TM_from_str "1RB0LC_1RC1RA_1RD1LA_1LE0RE_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1254: ~halts (TM_from_str "1RB1LF_1RC0RB_1LD1RA_---0LE_0RB0LB_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1255: ~halts (TM_from_str "1RB1RE_1RC0LC_1LD1LF_0RE0LD_0RC1RA_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1256: ~halts (TM_from_str "1RB1RA_1LC1LB_0LF0LD_0RE0LC_0RA---_1RD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1257: ~halts (TM_from_str "1RB---_0RC1LE_1RD1RC_1LB1LD_1LF1RF_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1258: ~halts (TM_from_str "1RB0LF_1LC0RE_1RD0LC_0RE---_1RA1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1259: ~halts (TM_from_str "1RB1RE_1RC0LF_1RD---_1LE1RA_0RA1LF_0RD0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1260: ~halts (TM_from_str "1RB0RA_1LC1RF_0RE0LD_1LC0LC_0RD1RA_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1261: ~halts (TM_from_str "1RB0RB_0LC1RD_1RA1LC_0LC0LE_---1LF_0RA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1262: ~halts (TM_from_str "1RB0RF_1RC---_1RD1LC_1LE1RA_0RF0LE_0RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1263: ~halts (TM_from_str "1RB0LE_1LC1RA_0LF0LD_0RA1RD_0RB1LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1264: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LE_0RC0LD_1RF1LF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1265: ~halts (TM_from_str "1RB1LC_0LC0RB_0LF1RD_1LE1LD_1LA1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1266: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB0LD_0LF1RF_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1267: ~halts (TM_from_str "1RB1RD_0RC0LD_1LD0RE_1LD0LA_1LF1RE_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1268: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA0RE_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1269: ~halts (TM_from_str "1RB0LA_1RC---_1RD1LE_1LC1LD_1LA0RF_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1270: ~halts (TM_from_str "1RB0RF_0RC0RB_0LD1RF_1LE---_1LD0LA_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1271: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0LA_1LC---_0RA1LE_1LC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1272: ~halts (TM_from_str "1RB0LC_1LC0RD_1RB1LC_---0RE_1LF1RE_0LC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1273: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD0LA_1LC0LE_0RB1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1274: ~halts (TM_from_str "1RB1LC_0RC---_1RD1RC_1RE1LD_1LF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1275: ~halts (TM_from_str "1RB1LB_1LC0RD_0LA1LA_1RF0RE_0LB1LD_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1276: ~halts (TM_from_str "1RB---_1RC1LF_1LD0RC_1RE0LD_1RF1RA_1LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1277: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_1RF0RE_1LB0RD_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1278: ~halts (TM_from_str "1RB---_0RC0LC_1RD1RF_1LE0LF_0RA0LE_1RC1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1279: ~halts (TM_from_str "1RB1LD_1LC1LD_0RE0RA_0LC0LD_1RF---_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1280: ~halts (TM_from_str "1RB---_1RC1LD_1LD1RE_0LF0RE_1RA1LD_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1281: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD1LC_0LB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1282: ~halts (TM_from_str "1RB1LD_1LC1RF_0LD0LB_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1283: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1LE1RF_0RF0LE_0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1284: ~halts (TM_from_str "1RB1RE_1RC1LE_1LD0RB_0RC0LD_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1285: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE1LF_1LC1RE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1286: ~halts (TM_from_str "1RB1RC_1LA1LD_0RF0RB_0LD0LE_0LA1RF_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1287: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD1RD_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1288: ~halts (TM_from_str "1RB0LE_0LC0RB_1LA1LD_1LE0LF_1LC1RE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1289: ~halts (TM_from_str "1RB1LC_1LC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1290: ~halts (TM_from_str "1RB1RA_1RC0RB_1LC0LD_1LF0LE_1RC---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1291: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD0RF_1LE1LA_0RB0LE_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1292: ~halts (TM_from_str "1RB1LE_0RC---_1RD1RC_1LA1LD_0LF1RF_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1293: ~halts (TM_from_str "1RB1LD_1RC0RD_1LD1RA_0RC0LE_0LF0LB_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1294: ~halts (TM_from_str "1RB1RA_1LC1RF_0RD0LC_1RE1LD_0RA1LA_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1295: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD1RE_1LA---_0RE0RF_0RB0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1296: ~halts (TM_from_str "1RB1LF_1RC1RA_1RD1RA_1LE0RD_0RB0LE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1297: ~halts (TM_from_str "1RB1RC_0RC---_1RD1RC_1RE1LD_1LF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1298: ~halts (TM_from_str "1RB1LC_1LA1RC_0LD0LA_1LE0RE_0RF1RA_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1299: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1LD_1LA1RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1300: ~halts (TM_from_str "1RB1RE_1LC1LB_---0RD_0RE1RD_1LF1RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1301: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD0RD_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1302: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_0RA0LE_0RF0LF_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1303: ~halts (TM_from_str "1RB1RA_0LC0LF_---1LD_1RA0LE_1LC1RF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1304: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LB_1RE0LD_1RF---_1LC1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1305: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LD_1RE---_1RF1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1306: ~halts (TM_from_str "1RB0LA_0RC0LF_1RD1RC_1LA1LE_1LB1LE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1307: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RE1RD_1RA0LF_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1308: ~halts (TM_from_str "1RB1LE_1LC1LF_0RD0LC_0RA1RA_1RD0LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1309: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA1RB_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1310: ~halts (TM_from_str "1RB---_0RC1LB_1RD1RC_1LE1LF_0RB0LE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1311: ~halts (TM_from_str "1RB1RE_0RC1LD_1LD1LA_0LA0LD_0RF---_0RE0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1312: ~halts (TM_from_str "1RB0LD_1RC1RE_0LA1RC_1LF1LA_0RC0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1313: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LB_1LE---_1LA1RF_0RC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1314: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LF_0LA1LF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1315: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_1RE---_0RA1LF_0LB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1316: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD1RE_0RC0LD_0RA---_1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1317: ~halts (TM_from_str "1RB1LA_0RC1LF_1LD1RF_0LE---_0RA0LE_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1318: ~halts (TM_from_str "1RB1LC_1RC1LB_1LD1RE_0RE0LD_0RF1RA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1319: ~halts (TM_from_str "1RB1LA_1RC1RB_1LD1LA_0LE0LD_0RF0RA_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1320: ~halts (TM_from_str "1RB1LA_1LA1RC_1RF1RD_0RE0LD_0RC---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1321: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA0LE_0LE0LF_1RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1322: ~halts (TM_from_str "1RB0LB_1LC0LB_---0RD_1LF1RE_1RD1LA_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1323: ~halts (TM_from_str "1RB1RD_1LC0LF_---0RD_1LF1RE_1RD0LA_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1324: ~halts (TM_from_str "1RB1LD_1RC0LF_1LA1RB_0RE0LD_1RF---_0RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1325: ~halts (TM_from_str "1RB1LD_1RC0RA_1LA0RE_0LA1RB_0RF1LC_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1326: ~halts (TM_from_str "1RB---_1LC0RF_1RE0LD_1LB1LD_0LA0RE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1327: ~halts (TM_from_str "1RB1LF_0RC1RC_1RD1RB_1RE---_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1328: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1329: ~halts (TM_from_str "1RB0LA_1LC0LD_1LD0LC_1RE0RB_0RF0RA_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1330: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RA0RF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1331: ~halts (TM_from_str "1RB0RA_1LC1RA_1RF1LD_0LE1LB_0LB---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1332: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LD_1LE1RA_0RD0LF_0LE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1333: ~halts (TM_from_str "1RB1RD_0LC0RB_1LE1LD_1LC0RA_0LF0LC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1334: ~halts (TM_from_str "1RB---_0LC0RB_0LE1LD_0LE1LA_1LF1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1335: ~halts (TM_from_str "1RB1LA_1RC1RF_1LD1RE_0RC0LD_0RA---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1336: ~halts (TM_from_str "1RB0RD_1RC1LE_1LA0RB_1RF1LC_0LB0LA_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1337: ~halts (TM_from_str "1RB0LD_1RC1LF_1LA---_1RA1RE_0RE0RB_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1338: ~halts (TM_from_str "1RB1LC_1LA1RF_0RD0LC_0RE1RD_1RA0LE_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1339: ~halts (TM_from_str "1RB1RA_1LC1RC_---0LD_1LE1LD_1RF1RA_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1340: ~halts (TM_from_str "1RB1RC_0RC1LC_1RD---_1RE0LA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1341: ~halts (TM_from_str "1RB0LE_1RC1LE_1LD1RD_0RC1RB_0LC1LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1342: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA0LE_1RF1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1343: ~halts (TM_from_str "1RB1RD_1LC0RA_0LE1RA_0RB1LF_0LF0LC_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1344: ~halts (TM_from_str "1RB1LA_0RC1LF_1RD1LA_1LE---_0RB0LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1345: ~halts (TM_from_str "1RB1RE_1LC0RB_0LA0LD_1LA1LD_1RF1RA_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1346: ~halts (TM_from_str "1RB1LC_1LC1RA_0LF0LD_1RE0LC_0RA---_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1347: ~halts (TM_from_str "1RB0LE_0LC---_0LA1RD_1LE0RF_0LB1RD_0RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1348: ~halts (TM_from_str "1RB1LF_1LC0RE_0RD0LC_0RB1RA_1RD---_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1349: ~halts (TM_from_str "1RB1LC_1LC1RA_---0LD_0RA0LE_0LF0RE_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1350: ~halts (TM_from_str "1RB1RA_0RC0LF_1LC1RD_0RE0LD_0RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1351: ~halts (TM_from_str "1RB1RF_1RC0RB_1LD0RD_0LE0LD_1LA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1352: ~halts (TM_from_str "1RB1LF_1LC0RD_0RB0LC_1RA1LE_1RD1RE_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1353: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE0LD_1LB0RD_0LB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1354: ~halts (TM_from_str "1RB1LE_0LB1RC_0LD0RC_0LE1LC_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1355: ~halts (TM_from_str "1RB1LA_1LC0RD_0RB0LC_1RE1LE_1LF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1356: ~halts (TM_from_str "1RB1RA_1RC0RB_1LD0RD_---0LE_0LF0LB_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1357: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RC_0RB0LD_1RF1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1358: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA1RB_0LD1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1359: ~halts (TM_from_str "1RB1RA_1RC0RF_1LD---_0LE1LE_1LA1LE_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1360: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LE---_0LF1RF_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1361: ~halts (TM_from_str "1RB1LA_1LC1LB_0RD0LC_1RE---_0RA1RF_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1362: ~halts (TM_from_str "1RB0LA_0RC1LD_1LA1LF_---0RE_1RC1RE_1LB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1363: ~halts (TM_from_str "1RB1RC_0LA0RB_1LD1RD_---0LE_1LF1LE_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1364: ~halts (TM_from_str "1RB1RD_1LC0RB_0RA0LC_1RE0RF_1RA1LE_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1365: ~halts (TM_from_str "1RB1LF_0RC1RC_0LD0RC_1LE---_0LA1LA_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1366: ~halts (TM_from_str "1RB1LE_1LC0RB_0LA1RD_---0LA_1LA1RF_0RD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1367: ~halts (TM_from_str "1RB0LA_1RC1LD_1LB1RE_0LF0RC_0RB1LA_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1368: ~halts (TM_from_str "1RB0LA_0RC1LF_1RD1RC_1LA1LE_1LB1LE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1369: ~halts (TM_from_str "1RB0LA_0RC0RD_1LA1LE_1RC1RD_1LF1LC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1370: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1LB_1LA1LD_1RF1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1371: ~halts (TM_from_str "1RB0LA_1RC1RE_1LD0LC_1LA0RD_1RF---_1RD1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1372: ~halts (TM_from_str "1RB1RF_0LC0RB_0LD1LB_1LE---_1LA1LE_1RD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1373: ~halts (TM_from_str "1RB1LE_1LC1RA_1RF1LD_1RD0RB_0LC0LE_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1374: ~halts (TM_from_str "1RB1RA_1RC0RF_1LD---_0LE1RE_1LA1LE_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1375: ~halts (TM_from_str "1RB0LA_0RC0RF_1RD1RC_1LA1LE_1LF1LE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1376: ~halts (TM_from_str "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1377: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB1LD_1RE0RB_---0RD_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1378: ~halts (TM_from_str "1RB1LC_1LC1LD_0LC0LD_0RE0RA_1RF---_1RE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1379: ~halts (TM_from_str "1RB0LF_1LC1LB_---0RD_1RA1RE_1LA1RD_0LD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1380: ~halts (TM_from_str "1RB---_0RC1RC_1RD1RC_1LE1LF_0RB0LE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1381: ~halts (TM_from_str "1RB---_1LC0RF_1RC0LD_1LB0LE_1LA0LC_0RF1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1382: ~halts (TM_from_str "1RB0RC_1LC1RB_1RA0LD_0RA0LE_1RC1LF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1383: ~halts (TM_from_str "1RB1LE_1LC0RF_0LA1RD_---0LA_1LA1RB_0RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1384: ~halts (TM_from_str "1RB0LA_0RC1LF_1RD1RC_1RE1LD_1LA1LB_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1385: ~halts (TM_from_str "1RB0LE_0LC---_0LA1RD_1LE0RF_0LB1RD_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1386: ~halts (TM_from_str "1RB0LD_0LC0RB_1LE1RD_1LA1RC_1LF1LE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1387: ~halts (TM_from_str "1RB0RD_1RC1LB_0RD0RA_1LE1RD_1RD0LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1388: ~halts (TM_from_str "1RB1RA_1RC1RE_1LD0RB_0RC0LD_1LF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1389: ~halts (TM_from_str "1RB---_1LC1LF_0LC1RD_1RA0RE_0RB0RD_1LF1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1390: ~halts (TM_from_str "1RB0LE_0RC1RB_1RD1RC_1LE1LD_1LF0LA_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1391: ~halts (TM_from_str "1RB1LD_1RC---_1LD1RA_0RD0LE_0RB0LF_0LD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1392: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1LD_1LA0RF_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1393: ~halts (TM_from_str "1RB1LD_1LB1RC_1RF1LD_0LD0LE_0RA0RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1394: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD---_1RE1LA_1LF0RC_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1395: ~halts (TM_from_str "1RB1RE_1LC1RA_1LA0LD_0RE1LA_1RF1LC_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1396: ~halts (TM_from_str "1RB---_0RC1LE_0RD1RC_1LA1LF_0RB0LE_1LD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1397: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LF1LA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1398: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD1LA_0RE0LD_1RF---_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1399: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD0LA_1RE---_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1400: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE1LE_0RF---_0RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1401: ~halts (TM_from_str "1RB1RE_1RC1LB_1LD1RA_0RB0LE_0RF0LD_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1402: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD1LD_1LA1RE_0RF0RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1403: ~halts (TM_from_str "1RB1RD_1LC0LF_---0RA_1RE1LF_1LE1RD_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1404: ~halts (TM_from_str "1RB1RA_1LB1LC_1LD0LF_0RE1RF_---0RD_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1405: ~halts (TM_from_str "1RB1RF_0LC0RB_0LD1LB_1LE---_1LA1LE_1RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1406: ~halts (TM_from_str "1RB1RE_1LC1LD_1LF0LD_0RE0LC_1RF---_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1407: ~halts (TM_from_str "1RB1RD_0RC1LA_1RD---_1RE1RD_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1408: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE1RF_1RA1RD_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1409: ~halts (TM_from_str "1RB0LF_1LC1RC_0RD0LC_0RE---_1RA1RE_1RE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1410: ~halts (TM_from_str "1RB0LA_0RC---_1RD1RC_1RE0LF_1LA0RC_1LE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1411: ~halts (TM_from_str "1RB1RA_1RC1RE_1LD0RA_---1LB_1LF0LD_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1412: ~halts (TM_from_str "1RB1RF_1LC0RB_0LA1RD_---0LE_1LA1LE_1RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1413: ~halts (TM_from_str "1RB1LC_0RC1LE_1LD0RB_1RA1RB_0LD0LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1414: ~halts (TM_from_str "1RB0LD_0RC0RE_1LC0LA_0RA1LD_1LF1RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1415: ~halts (TM_from_str "1RB1LE_1RC---_1LD0RA_0RB0LD_1RF1LA_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1416: ~halts (TM_from_str "1RB1RF_0RC0LB_0RD1RA_1RE1RD_1LC1LE_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1417: ~halts (TM_from_str "1RB1RC_1LC---_0LE1LD_0LC0RD_1LF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1418: ~halts (TM_from_str "1RB1LD_1LC1LF_0RD0LC_1RE0LF_0RA1RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1419: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD1LE_0LE---_1LA1RF_1RE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1420: ~halts (TM_from_str "1RB1LE_0RC---_1LD1RA_0RA0RF_0LD0LC_0LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1421: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LA_1LE0RC_0RD0LE_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1422: ~halts (TM_from_str "1RB1LD_1RC1RA_1LA1RA_1RE0LA_---0RF_1RE1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1423: ~halts (TM_from_str "1RB1LD_0LC1RF_0LD1LC_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1424: ~halts (TM_from_str "1RB0LF_1RC---_0RD1RD_1RE0RB_1LA1LF_1LC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1425: ~halts (TM_from_str "1RB1RA_1RC1LA_1RD1LF_1LE0RB_0RD0LE_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1426: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE0LE_1LA1RE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1427: ~halts (TM_from_str "1RB---_1RC1LB_1RD1RF_1LE0RA_0RC0LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1428: ~halts (TM_from_str "1RB1LC_1RC1RB_0LD1LD_1LE1LA_1RF---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1429: ~halts (TM_from_str "1RB1RD_1LB1LC_0RA0LE_1RA1RD_0LF0RA_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1430: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB1LD_1RD0RE_---1LC_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1431: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE0LE_1RF1RC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1432: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE0LE_1RF1RD_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1433: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RD0RF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1434: ~halts (TM_from_str "1RB---_0RC1RC_1RD0LD_1LE1RF_0RA0LE_1LC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1435: ~halts (TM_from_str "1RB1RC_0RC0RB_1RD1LE_1LA1RC_0LF0LB_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1436: ~halts (TM_from_str "1RB1LC_1LB1RA_0LF0LD_1RE0LC_1LE1RF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1437: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_1LF0LE_0RA1RD_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1438: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LE_1RE0LD_0RA1LF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1439: ~halts (TM_from_str "1RB1RF_1RC---_1RD1LC_1LE1RA_0RF0LE_0RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1440: ~halts (TM_from_str "1RB0LE_0LC0RB_1LF1RD_1LE1LD_1LC1RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1441: ~halts (TM_from_str "1RB1RE_0RC0RA_1LC0LD_0RA0LD_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1442: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD1RE_1LA---_0RE0RF_0RB0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1443: ~halts (TM_from_str "1RB0LC_1LC0RD_0LE1RB_0RB1LC_0LF---_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1444: ~halts (TM_from_str "1RB1RA_0RC0RB_1LD1RD_0LE---_1LF0LC_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1445: ~halts (TM_from_str "1RB1LA_1LA0RC_---0RD_1LE1RD_0LA0RF_0LE1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1446: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LF_1RA1RD_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1447: ~halts (TM_from_str "1RB1RC_0RC---_1LD1LF_0RA0LE_0RF0LD_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1448: ~halts (TM_from_str "1RB---_1LC1RF_1LA1LD_0LE1LE_1LB0RF_0LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1449: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1LB_1LA1LD_1RF1RE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1450: ~halts (TM_from_str "1RB0LF_1RC---_1RD0RD_1LE1RA_1RC1LA_0RE0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1451: ~halts (TM_from_str "1RB0RC_0RC---_1RD1LC_1LE1RF_0RB0LE_1RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1452: ~halts (TM_from_str "1RB0LB_1RC1LB_0LA0RD_0LA0RE_1LD1RF_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1453: ~halts (TM_from_str "1RB1LA_0RC1LB_1LD1RF_0LE---_0RA0LE_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1454: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1455: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA0RE_0LD1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1456: ~halts (TM_from_str "1RB1LE_1LC1RA_0RA0LD_1RC0LC_1LF0LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1457: ~halts (TM_from_str "1RB1LA_1RC1LE_1LD0RA_0RB0LD_1RA1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1458: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1LF1RC_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1459: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RE_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1460: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE0LD_1LB0RD_0LB1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1461: ~halts (TM_from_str "1RB0RF_1LC0RE_1RE0LD_0RA1LC_1RA1RC_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1462: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1RE_0RE0LD_0RF1LA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1463: ~halts (TM_from_str "1RB1LD_0RC1RF_1LC0LA_0RD0LE_0RB1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1464: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LF0RC_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1465: ~halts (TM_from_str "1RB0LD_1RC1LD_1LD1RF_0RC1LE_---0LA_0RC1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1466: ~halts (TM_from_str "1RB0LA_0RC0RD_1LA1LE_1RC1RD_1LF1LE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1467: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LC_1LE1LF_1LA1RF_1LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1468: ~halts (TM_from_str "1RB1RA_0LC0RE_1LF1LD_1LA1LC_0LA0RB_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1469: ~halts (TM_from_str "1RB0LD_1RC1RA_0LD1RF_0RE1LA_1RE0RB_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1470: ~halts (TM_from_str "1RB0LD_1LB1RC_1RA1LA_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1471: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_---0RE_1LF1RE_0LA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1472: ~halts (TM_from_str "1RB1LA_1LC1RD_0RD0LC_0RB1RE_1RF1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1473: ~halts (TM_from_str "1RB---_1RC1LE_1LD0RB_0RC0LD_1RF0LE_1RF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1474: ~halts (TM_from_str "1RB1RA_1RC0RC_1LD1RF_---1LE_0RA0LE_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1475: ~halts (TM_from_str "1RB1RF_0LC1RA_1LA0LD_0RC0LE_---1LC_0RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1476: ~halts (TM_from_str "1RB1RB_0LC0RB_0LD1LB_1LE0RD_1LF---_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1477: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LF_1LA---_1LA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1478: ~halts (TM_from_str "1RB0RB_1RC1LF_1RD1LC_1LE1RA_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1479: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA0RE_0LD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1480: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LD_1LE1RA_0LE0LF_0RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1481: ~halts (TM_from_str "1RB1LD_1LC1LE_1RF1RA_0LD0LE_0RF0RA_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1482: ~halts (TM_from_str "1RB1LF_1LC1RE_0RD0LC_0RE---_1RA1RD_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1483: ~halts (TM_from_str "1RB0RD_1LC0RA_1RB1LC_1LE1RD_1LB0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1484: ~halts (TM_from_str "1RB0LE_1LC0RD_0RB0LC_1RA1RD_1LF1LE_0RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1485: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_1LE1RA_1RF0LC_0LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1486: ~halts (TM_from_str "1RB1RA_1LC1LB_0LE0LD_0RE0LD_0RF---_1RA1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1487: ~halts (TM_from_str "1RB1LD_1LC1LF_1RE0LD_0RE0LC_1RF---_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1488: ~halts (TM_from_str "1RB1LF_1LC1RE_1LD0LB_0RB0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1489: ~halts (TM_from_str "1RB---_0RC1LD_0LD1RE_1RE1RD_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1490: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_0RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1491: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1RE_1LF1RD_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1492: ~halts (TM_from_str "1RB0RD_1LC0RD_0LE1RA_0RB1LC_0LC1LF_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1493: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA---_0LA1RF_0RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1494: ~halts (TM_from_str "1RB1LF_1RC1RA_1RD---_1LE0RA_0RB0LE_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1495: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LD1LF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1496: ~halts (TM_from_str "1RB0RB_1RC0LD_1LB1RE_0RE0LB_1RF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1497: ~halts (TM_from_str "1RB0LF_1LC1LB_---0RD_1RA1RE_1LA1RD_1RF0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1498: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1RE---_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1499: ~halts (TM_from_str "1RB0LB_1LC0LA_---0RD_1LF1RE_1RD1LA_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1500: ~halts (TM_from_str "1RB1RE_0RC1LF_1LD1LC_0RA0LD_1RC---_0LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1501: ~halts (TM_from_str "1RB0RD_0RC0LB_0RD---_1RE1LD_1LB1RF_1RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1502: ~halts (TM_from_str "1RB0LE_1LC1RF_---1RD_0LA1RD_1LB1LA_0RD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1503: ~halts (TM_from_str "1RB0LB_1RC1LB_0LD0RE_---1RE_0LA0RF_1LE1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1504: ~halts (TM_from_str "1RB---_1RC1RB_0LD0RC_0LF1LE_1LF1LD_1LB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1505: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB1LC_0LF0RC_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1506: ~halts (TM_from_str "1RB0LB_1RC1LB_0RD0RF_1LE1RD_1RD0LA_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1507: ~halts (TM_from_str "1RB1LC_1LC1RA_---0LD_0RE0LE_0LF0RE_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1508: ~halts (TM_from_str "1RB0RB_0LC0LE_1RD1LC_---1RA_0RA1LF_0RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1509: ~halts (TM_from_str "1RB1LF_1LC1RA_0RB1LD_1RD0RE_---1RA_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1510: ~halts (TM_from_str "1RB---_1RC1RB_1RD1LC_1RE1RB_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1511: ~halts (TM_from_str "1RB1LA_1LC1RD_0RD0LC_0RB1RE_1RF1LB_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1512: ~halts (TM_from_str "1RB1RE_1LC0LF_---0RD_1LA1RE_1RD1LF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1513: ~halts (TM_from_str "1RB0LF_1LC1RC_0RD0LC_0RE---_1RA1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1514: ~halts (TM_from_str "1RB0LA_1LC1RD_1LF0RD_1RE1LA_0RB0LC_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1515: ~halts (TM_from_str "1RB1LA_0LA0RC_1LD0RE_1LA0LA_1LF1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1516: ~halts (TM_from_str "1RB1LA_0RC1RC_1RD1RC_1LE1RF_0RA0LE_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1517: ~halts (TM_from_str "1RB1LA_1LC0RE_0LA0LD_1RE0LA_0RC1RF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1518: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LC_1LA1RD_1LD1LF_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1519: ~halts (TM_from_str "1RB0LA_1RC0RF_1RD---_1LE1LD_1LA1LB_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1520: ~halts (TM_from_str "1RB1LC_0LA1RD_1LA1RE_1RF0RE_1LB0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1521: ~halts (TM_from_str "1RB---_0RC1RD_0LD1RE_1RE1RB_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1522: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA0LD_0RE0LD_0RF---_1RC1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1523: ~halts (TM_from_str "1RB1RD_1LC0RD_0RA0LC_1RE1RD_1RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1524: ~halts (TM_from_str "1RB1LE_0LC0RB_1LD1LC_0LE---_1LF1RF_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1525: ~halts (TM_from_str "1RB1RA_1RC1LF_1RD1LC_1LE0RB_0RD0LE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1526: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD1RB_1LA1RE_0RF0RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1527: ~halts (TM_from_str "1RB1LC_1LB1RA_---0LD_0RA0LE_0LF0RA_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1528: ~halts (TM_from_str "1RB1LD_0LC1RD_0LE0RD_1LE0RC_1LF---_1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1529: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0RA0LD_1RC1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1530: ~halts (TM_from_str "1RB1LE_1RC1LB_1RD1RA_1RE---_1LF0RB_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1531: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RF_1LA1LD_0RE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1532: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA0RF_1LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1533: ~halts (TM_from_str "1RB0LF_0RC1LA_0RD---_0RE1LA_1LC0RB_0LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1534: ~halts (TM_from_str "1RB1LE_1LC1RA_0LF0LD_0RA0RD_0LC0LE_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1535: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE0RF_0LF1LD_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1536: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0RD_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1537: ~halts (TM_from_str "1RB---_1LC1LB_0LF1RD_0RA0RE_0RB0RD_0LC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1538: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RF_0RE0LD_1RA0RA_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1539: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD0RB_0RE0LD_1RA1LF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1540: ~halts (TM_from_str "1RB---_0LC0RB_0LE1LD_0LC1LA_1LF1LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1541: ~halts (TM_from_str "1RB1RE_1RC0LC_1LD1LC_0RE0LD_0RF1RA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1542: ~halts (TM_from_str "1RB0RB_1LA1RC_1LD0RD_0RA0LE_1LA1LF_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1543: ~halts (TM_from_str "1RB---_0RC0LD_1RD1LF_1RE0LB_1LC1RD_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1544: ~halts (TM_from_str "1RB0RA_1LC1RF_0RE0LD_1LC0LC_0RB1RA_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1545: ~halts (TM_from_str "1RB1RE_1RC0RC_1LC1LD_0RA0LD_1RA0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1546: ~halts (TM_from_str "1RB1LE_1RC1LB_1LD1RA_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1547: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD1LB_1LA0LF_0LD1RB_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1548: ~halts (TM_from_str "1RB1LF_0RC1LA_0RD0RB_1LE---_0LE1RA_1LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1549: ~halts (TM_from_str "1RB1LA_0RC1LB_1RD1RC_1LE1RF_0RA0LE_0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1550: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_0RF1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1551: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RC_0RB0LD_1RA1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1552: ~halts (TM_from_str "1RB1LD_1RC0RC_1LA1RF_---0LE_0RA0LD_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1553: ~halts (TM_from_str "1RB1LE_1LC1LE_---0LD_0RE0LC_1RF0LE_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1554: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RD1RF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1555: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LB_1LA1RE_0RF0RD_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1556: ~halts (TM_from_str "1RB0RC_1RC0LD_1LB1RC_---0LE_1RF1LE_1RB0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1557: ~halts (TM_from_str "1RB0LE_1RC---_1RD0RF_1LA0RB_0LF1LC_0LD0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1558: ~halts (TM_from_str "1RB0LA_1RC1LE_1RD---_1LB0RB_0LA0LF_0LB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1559: ~halts (TM_from_str "1RB1LC_1RC1RB_1LD1LA_0RF0LE_1RF0LD_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1560: ~halts (TM_from_str "1RB0LF_0LC0RB_1LA1LD_1LE1LC_1RC1RE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1561: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1LC---_1RF0RF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1562: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RF1RE_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1563: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RD_1LA1RF_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1564: ~halts (TM_from_str "1RB1LD_1LC1LB_0RD0LC_0RE0LE_1RF1RC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1565: ~halts (TM_from_str "1RB1RC_0RC---_1LD1RA_0LE1LF_0RA0LE_1RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1566: ~halts (TM_from_str "1RB1RD_0LC1RD_0LE1LA_1LB0RD_1LE0RF_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1567: ~halts (TM_from_str "1RB0RB_0RC0RB_1LD0RE_0LD1RA_0RF---_1LF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1568: ~halts (TM_from_str "1RB0LA_0RC1RC_1RD1LE_1LA0RD_0LF0LE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1569: ~halts (TM_from_str "1RB---_1RC1LD_1LC1RB_1RF0LE_1LF0LD_0RA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1570: ~halts (TM_from_str "1RB---_1RC1LB_0RD0RC_1LE1LF_0LE0RB_1LF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1571: ~halts (TM_from_str "1RB1LE_1RC1RE_1LD---_1LA0LA_1LC0RF_0LC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1572: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RA1LD_1RD1RF_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1573: ~halts (TM_from_str "1RB---_1LC1LB_1LD1RC_1RF0LE_1LA0RE_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1574: ~halts (TM_from_str "1RB1RE_0LC0RD_1LC1LA_0LC0LA_---0RF_0RB0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1575: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0RC_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1576: ~halts (TM_from_str "1RB1RC_0RC---_1RD1RE_1RE1LD_1LF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1577: ~halts (TM_from_str "1RB1LD_1LC1RF_0LD0LD_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1578: ~halts (TM_from_str "1RB1RC_0RC---_1RD1LE_1RE1LD_1LF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1579: ~halts (TM_from_str "1RB1LD_1LC0RE_1LE0LD_1LA1RB_1RF0RB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1580: ~halts (TM_from_str "1RB0LE_1RC0RC_1LD1RC_---0LA_1RF1LE_0LE0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1581: ~halts (TM_from_str "1RB1RD_1LC0RB_0RA0LC_1RE1RF_1RA1LE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1582: ~halts (TM_from_str "1RB0LF_0RC1RE_1LD1LA_0RB0LD_1RC1LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1583: ~halts (TM_from_str "1RB1RB_0LC0RB_0LD1LC_1LE0RD_1LF---_1RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1584: ~halts (TM_from_str "1RB1LC_1RC1RB_1RD1LA_1RE---_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1585: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LA1RE_1LF1RE_1LD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1586: ~halts (TM_from_str "1RB1LF_1LC0RD_0RA0LC_1RE---_1RA1LE_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1587: ~halts (TM_from_str "1RB1RD_1LC1LE_0LA1RD_0RD0RB_0LF---_0LE0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1588: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RE_0RA0LD_1RA1LE_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1589: ~halts (TM_from_str "1RB1LA_1LA0RC_0LA0RD_1LE1RD_1RF0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1590: ~halts (TM_from_str "1RB1LA_1RC0RC_1RD0RD_1LE1RD_---0LF_1RC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1591: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LF_1RF1RC_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1592: ~halts (TM_from_str "1RB1RC_0RC---_1LD1RA_0LE1RF_0RA0LE_1RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1593: ~halts (TM_from_str "1RB0LB_1RC1LD_0RD0RB_1LE0LC_0LF1RA_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1594: ~halts (TM_from_str "1RB1RA_1LB1LC_1RD0LF_0RA1LE_---0RA_0LE0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1595: ~halts (TM_from_str "1RB1RA_1LC1LD_0RA0LC_0LF0LE_0RB1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1596: ~halts (TM_from_str "1RB---_0RC1LC_1RD---_1RE1RD_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1597: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_0LE1RA_1RE1LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1598: ~halts (TM_from_str "1RB1RD_1RC---_0RD1LD_1RE1RA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1599: ~halts (TM_from_str "1RB1LC_1LB1RA_---0LD_0RA0LE_0LF0RE_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1600: ~halts (TM_from_str "1RB1LE_1LC0RC_1RD1LC_---0LA_1LA1RF_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1601: ~halts (TM_from_str "1RB0RF_0RC0RE_1LD---_0LD1RA_1LE0RA_1LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1602: ~halts (TM_from_str "1RB1LA_1RC1LE_1LD0RA_0RB0LD_1RF1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1603: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD1LC_0LB1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1604: ~halts (TM_from_str "1RB0RE_0RC1RA_1LD0LD_0LE0LC_0RF1RC_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1605: ~halts (TM_from_str "1RB---_0RC1RE_1LD1LF_0RB0LD_1RC1RE_1LA1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1606: ~halts (TM_from_str "1RB1RE_1RC---_1LD0RC_0RA0LD_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1607: ~halts (TM_from_str "1RB---_0RC1RC_1RD1LF_1LE1LB_1RA0LF_0RA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1608: ~halts (TM_from_str "1RB0RE_0LC1RE_---1LD_1RA1LC_0LD0LF_0RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1609: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA0RE_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1610: ~halts (TM_from_str "1RB1LF_1LC1RD_1LA0LB_0LE0RD_0LF---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1611: ~halts (TM_from_str "1RB1RA_1RC1LD_1LC1LB_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1612: ~halts (TM_from_str "1RB0LB_0LC0RD_---1LD_1LE1RF_1RD1LF_0RA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1613: ~halts (TM_from_str "1RB1LF_0RC1RC_0LD0RC_1LE---_0LA0RA_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1614: ~halts (TM_from_str "1RB1RA_0RC0RD_0LC0LD_1LE0RB_0LF---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1615: ~halts (TM_from_str "1RB---_1RC0LB_1RD0RF_1LE1RA_0RB1LF_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1616: ~halts (TM_from_str "1RB0LF_0RC0LB_1LD0RB_0LE---_0LA1RB_0LD0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1617: ~halts (TM_from_str "1RB1LC_1RC1LB_1LD1RE_0RE0LD_0RF1RA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1618: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD0LE_1LE---_1RA0RF_1LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1619: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1RA_1LE1RF_0RD0LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1620: ~halts (TM_from_str "1RB1RD_1LC0RA_1RA0LB_0RE---_0LE0LF_1LE1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1621: ~halts (TM_from_str "1RB1LD_0RC---_1RD1RC_1LE1LA_1RC0LF_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1622: ~halts (TM_from_str "1RB1RA_1LC1LB_1LD0LC_1RE1LE_---0RF_0RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1623: ~halts (TM_from_str "1RB1RA_1RC0LF_1LD0RA_0RE0LD_1LB---_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1624: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_0LE0LF_0LC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1625: ~halts (TM_from_str "1RB0LF_1LC0RF_---1RD_1LB1RE_0RD1LA_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1626: ~halts (TM_from_str "1RB1RF_1LC1RE_1LD1LC_1LA0LC_0LD0RE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1627: ~halts (TM_from_str "1RB1RE_1LC0RD_---1LA_1RA1RD_0LF0LC_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1628: ~halts (TM_from_str "1RB0LA_0RC1LD_1LA1LF_---0RE_1RC1RE_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1629: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LB0RF_0LA0RE_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1630: ~halts (TM_from_str "1RB1RD_1LC0LF_---0RA_1RE1LF_1LA1RD_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1631: ~halts (TM_from_str "1RB1LE_1RC0RC_1LD1RC_---0LE_0RB0LF_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1632: ~halts (TM_from_str "1RB1LC_0LA1LC_1LA1RD_1LB0RE_1RF0RD_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1633: ~halts (TM_from_str "1RB0LC_1LA---_0RD0LF_1RD0RE_1RA0LA_0LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1634: ~halts (TM_from_str "1RB1RA_0RC1LF_1LC1RD_0RE0LD_0RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1635: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD1LB_1LA1LF_0LD1RB_1RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1636: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE0LF_0RF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1637: ~halts (TM_from_str "1RB1LE_0RC1RE_1LD0LA_1LC---_0RE0LF_0RB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1638: ~halts (TM_from_str "1RB0LB_0LC1LD_---1LD_1LE1RF_1RD1LF_0RA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1639: ~halts (TM_from_str "1RB1LA_1RC1RD_0LA0LE_---0RC_0RB1LF_0RD1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1640: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LB_1LE---_1LA1RF_1RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1641: ~halts (TM_from_str "1RB---_1LB1RC_1RA1LD_0LE0RC_1RE0LF_0RC0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1642: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE1LB_1LB0RD_0LB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1643: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE0LF_0RF---_0RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1644: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD1RD_0RE0LD_0RF---_1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1645: ~halts (TM_from_str "1RB1LC_1LC1LE_0LC0LD_1RA1RF_0RF0RA_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1646: ~halts (TM_from_str "1RB1LC_1LC1RA_---0LD_0RA0LE_0LF0RA_0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1647: ~halts (TM_from_str "1RB0LE_0RC1RC_1RD1RC_1LA1LF_0RB0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1648: ~halts (TM_from_str "1RB1RA_1RC0RA_1LD1LC_1LF1LE_0RB0LE_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1649: ~halts (TM_from_str "1RB0LC_1RC1RD_1LA0RB_0RE---_0LE0LF_1LE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1650: ~halts (TM_from_str "1RB1LD_0RC1LA_0RD1RC_1LE1LA_0LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1651: ~halts (TM_from_str "1RB1RF_0LC1LC_1LD1LB_1LE---_1RA1RE_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1652: ~halts (TM_from_str "1RB1RC_0RC---_1RD1RC_1RE1LD_1LF1RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1653: ~halts (TM_from_str "1RB1RA_1LC1LB_1LF0LD_0RE0LF_0RA---_1RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1654: ~halts (TM_from_str "1RB0RA_0LC1LB_---1LD_0RE0LD_1RA1RF_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1655: ~halts (TM_from_str "1RB---_0RC0LB_0RD---_1RE1RD_1LF1LE_1LC0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1656: ~halts (TM_from_str "1RB1LF_1LC1RA_0RD0LC_0RE---_1RA1RD_0LD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1657: ~halts (TM_from_str "1RB0RB_1LC0RD_0LE1RD_0LA1RD_---0LF_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1658: ~halts (TM_from_str "1RB---_1LC1LF_0LE1RD_0RA0RB_0LC1RA_0LF0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1659: ~halts (TM_from_str "1RB---_1LC0RD_0RA0LC_1RA1LE_1RF0LE_1RF1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1660: ~halts (TM_from_str "1RB1LD_1LC1LF_0RA1RA_0RE0LD_1RC---_1RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1661: ~halts (TM_from_str "1RB1LC_1LB1RA_1LF0LD_1RE0LC_0RA0LE_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1662: ~halts (TM_from_str "1RB1LD_1RC---_1LD1RA_0LE0RA_0RA0LF_0RD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1663: ~halts (TM_from_str "1RB1LE_1LC1RF_1LA0LD_0LE---_1LC0RE_0LD0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1664: ~halts (TM_from_str "1RB1LE_1LC1RA_0RA0LD_1RC0LD_0LF0LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1665: ~halts (TM_from_str "1RB1RA_1RC---_1RD0LF_1LE0RB_0RD0LE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1666: ~halts (TM_from_str "1RB---_0RC1RD_0LD1RE_1RE1RD_1LF1LE_0RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1667: ~halts (TM_from_str "1RB1LE_0LC1RD_0LE1LD_0LC0RD_1LF0RE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1668: ~halts (TM_from_str "1RB0LD_1RC0LA_1LB1RC_1RE1LD_0RC0RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1669: ~halts (TM_from_str "1RB1RC_1RC---_0RD1RD_1RE1LA_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1670: ~halts (TM_from_str "1RB1LF_0RC1LC_1RD1RC_1RE---_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1671: ~halts (TM_from_str "1RB1LF_0RC1RC_1RD1RC_1RE---_1LA1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1672: ~halts (TM_from_str "1RB0LC_1LC0RD_0LA1RB_0RE1LC_0RF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1673: ~halts (TM_from_str "1RB0RA_0RC---_1LC1RD_0LE0LD_1LF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1674: ~halts (TM_from_str "1RB1LA_1LC0RE_0LA0LD_1RE0LA_0RC0RF_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1675: ~halts (TM_from_str "1RB1RF_0RC0RE_1LD---_0LD1RA_1LE1LA_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1676: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_1LA1LF_0LA1RF_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1677: ~halts (TM_from_str "1RB0RD_1RC1RB_1LD1LC_0RE0LD_0RF0LF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1678: ~halts (TM_from_str "1RB---_1RC1LE_1LD0RB_0RC0LD_1RF1LE_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1679: ~halts (TM_from_str "1RB0RB_1LC1LF_0LD1RA_0LC1RE_0RA---_0LF0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1680: ~halts (TM_from_str "1RB1LE_1LC1RA_1RF1LD_0RB0LE_0LF0LD_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1681: ~halts (TM_from_str "1RB1RB_1LC1RE_---0LD_0RA0LF_1RA0LA_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1682: ~halts (TM_from_str "1RB0LC_1LC0RD_0LE1RB_0RB1LC_0LF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1683: ~halts (TM_from_str "1RB1LD_0LC0RB_1LF1LD_1LE1RE_1LA0RE_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1684: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1LD_1LF1RE_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1685: ~halts (TM_from_str "1RB1LD_0RC1LF_1RD1RC_1LE1LA_0RB0LE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1686: ~halts (TM_from_str "1RB1RD_1RC---_0RD1LE_1RE1RA_1LF1LC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1687: ~halts (TM_from_str "1RB0RB_1LB1LC_0RD0LC_1RA1RE_1RD0LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1688: ~halts (TM_from_str "1RB0LF_0LC0LF_1RF1LD_0LE1RF_1LC---_0RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1689: ~halts (TM_from_str "1RB---_1RC1RB_1RD1LC_1LE0RF_0RD0LE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1690: ~halts (TM_from_str "1RB---_0RC1LE_0RD1RC_1LA1LF_0RB0LE_1RD1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1691: ~halts (TM_from_str "1RB0LF_0RC1LD_1LA0RB_0LC1LE_0LE1RA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1692: ~halts (TM_from_str "1RB1RF_1RC1RD_1LD0LF_---0LE_0LA1LE_1RA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1693: ~halts (TM_from_str "1RB1RA_1LC1LE_1RF0LD_1LE---_1LA1LB_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1694: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_---0LE_0RA0LF_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1695: ~halts (TM_from_str "1RB---_0RC1LF_1RD1RC_1LE1LB_0RA0LE_0LD1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1696: ~halts (TM_from_str "1RB0LF_1RC---_0RD1RD_1RE1LA_1LC1LF_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1697: ~halts (TM_from_str "1RB1RF_1RC0RD_1LD1LF_---1LE_0RA0LE_1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1698: ~halts (TM_from_str "1RB0RB_1LC1RD_---1LD_1RE0LF_1RA0RB_0RE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1699: ~halts (TM_from_str "1RB1LB_1RC0LB_1LD1RA_0RA0LE_---1LF_0RF1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1700: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RA_1LF1LE_0RF1LA_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1701: ~halts (TM_from_str "1RB0LA_0RC0RF_1LD1LC_1LE1LA_---0RB_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1702: ~halts (TM_from_str "1RB1LF_1LB1RC_0LD0RC_1LE---_0LA0RA_1LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1703: ~halts (TM_from_str "1RB0RE_1RC1RB_1LD1LC_0RE0LD_0RF1LA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1704: ~halts (TM_from_str "1RB1LB_0RC0LF_1RD0LC_1RE---_1LA1RC_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1705: ~halts (TM_from_str "1RB0LA_0RC0RC_1RD1RC_1LA1LE_1LF1LE_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1706: ~halts (TM_from_str "1RB0RC_1LA---_1LE1RD_1RC1LF_1RA0LE_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1707: ~halts (TM_from_str "1RB0RC_1RC0RB_1LD0LA_0LF0LE_1LA0RE_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1708: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA1RD_0RE1LE_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1709: ~halts (TM_from_str "1RB0RD_1LC1LF_0LE1RA_0RB1LD_0LC---_0LF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1710: ~halts (TM_from_str "1RB0LA_1LC1RD_1LE0RD_1RE1LA_0RB0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1711: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_---0LE_0RF0LF_0LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1712: ~halts (TM_from_str "1RB1LF_1LC1RA_1RD0LC_1LD1RE_---0RA_0LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1713: ~halts (TM_from_str "1RB1RA_1RC0RF_1LD---_0LE1RD_1LA1LE_0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1714: ~halts (TM_from_str "1RB1RE_1RC0LC_1LD1LC_0RE0LD_0RF1RA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1715: ~halts (TM_from_str "1RB1RA_1LB1LC_0RA0LD_0LE0RA_0RA0LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1716: ~halts (TM_from_str "1RB1LA_1LC0RC_1RD0RD_1LE1RD_---0LF_1RC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1717: ~halts (TM_from_str "1RB1RA_1RC1LF_1RD1LC_1LE0RB_0RD0LE_1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1718: ~halts (TM_from_str "1RB---_1LC1LD_0RE0LD_1RE0LC_1RF1RA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1719: ~halts (TM_from_str "1RB0RD_1RC1LE_1LA0RB_0RF1LC_0LB0LA_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1720: ~halts (TM_from_str "1RB---_1RC1LD_1LD1RB_1RF0LE_1LF0LD_0RA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1721: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_0RE1LB_1LB0RD_0LB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1722: ~halts (TM_from_str "1RB1RA_1RC1LB_1RD1RA_1RE---_1LF0RE_0RC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1723: ~halts (TM_from_str "1RB1LA_0RC1RF_1LD1RF_0LE---_0RA0LE_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1724: ~halts (TM_from_str "1RB0RF_1RC1RB_1LD1LC_0RE0LD_0RF0LF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1725: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD0LE_0LB0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1726: ~halts (TM_from_str "1RB1RC_1LC0LF_---0LD_0LE1LD_1RA1RF_1RE0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1727: ~halts (TM_from_str "1RB0LA_0RC---_1RD1LC_1LE1RF_0RB0LE_1RC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1728: ~halts (TM_from_str "1RB1RE_1LC0RE_0RD0LC_1RA1LF_1RD1LD_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1729: ~halts (TM_from_str "1RB1RF_0LC0RD_0LA1LA_0LE0RB_1LC---_1LE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1730: ~halts (TM_from_str "1RB1LC_1LA1RB_0LD1LD_1LE1LA_1RF---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1731: ~halts (TM_from_str "1RB1LF_1LC0RD_1LD0LC_1RE0RB_---0LA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1732: ~halts (TM_from_str "1RB1RA_0RC1LD_1LC1LD_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1733: ~halts (TM_from_str "1RB---_0RC1LD_1LD---_0LE0LD_1RA1RF_0RF0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1734: ~halts (TM_from_str "1RB1RE_1RC---_1LD0RA_0RB0LD_1LF1RA_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1735: ~halts (TM_from_str "1RB0LA_1RC---_1RD0RF_1LE1LD_1LA1LC_1RE1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1736: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LC_0RE0LD_1RF---_0RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1737: ~halts (TM_from_str "1RB0LF_0LC---_0LA1RD_1LC0RE_0RD0LE_0LB1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1738: ~halts (TM_from_str "1RB0RD_1LC1LF_0LE1RA_0RB1LF_0LC---_0LF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1739: ~halts (TM_from_str "1RB1RA_1LC1LD_0RA0RB_0LE0LF_0RB0LC_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1740: ~halts (TM_from_str "1RB1LE_1RC---_0RD1RD_1RE1RD_1LF1LA_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1741: ~halts (TM_from_str "1RB0RF_1RC0LB_0LD1RE_1RA0LC_1LD0RA_---1RC") c0.
Proof. solve_loop1_0 2000%N. Time Qed.

Lemma tm1742: ~halts (TM_from_str "1RB1RF_1RC---_1RD1LC_1LE1RF_0RF0LE_0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1743: ~halts (TM_from_str "1RB0LD_1RC1RE_0LA0LD_1LF1LA_0RC0RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1744: ~halts (TM_from_str "1RB0LD_0RC1LD_1LD---_0LE0LA_1RA1RF_0RF0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1745: ~halts (TM_from_str "1RB0RF_1RC1LA_0LD1RA_---1LE_0LA1LF_1RC0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1746: ~halts (TM_from_str "1RB1RD_1LC0LB_---0RA_1RE1LB_1LF0RE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1747: ~halts (TM_from_str "1RB0LD_0RC1RE_1LD0RB_1LA1RB_1RF0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1748: ~halts (TM_from_str "1RB1LD_0RC1RF_1LC0LA_1LD0LE_0RB1LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1749: ~halts (TM_from_str "1RB1LB_1LC1RD_1LA1LC_1LE0RB_---0LF_1LE1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1750: ~halts (TM_from_str "1RB1RF_1LC1RC_0LE1LD_0LB0RD_1LA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1751: ~halts (TM_from_str "1RB---_0RC1RC_1RD1LE_1LB1LF_0RA0LE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1752: ~halts (TM_from_str "1RB1LA_1LA0RC_0LE0RD_1LE1RF_0LA0LB_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1753: ~halts (TM_from_str "1RB1LF_1LC0RC_0RD0LC_0RE---_1RA1RE_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1754: ~halts (TM_from_str "1RB1LF_1LC---_1RA1RD_0RD0RE_0RB1LC_0LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1755: ~halts (TM_from_str "1RB0LF_1RC0LE_0RD1RE_1LA0RD_0RC0LA_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1756: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE1LF_0LE0RF_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1757: ~halts (TM_from_str "1RB1RF_0LC0RB_1LD1LC_0LE1LE_1LA1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1758: ~halts (TM_from_str "1RB---_0LC0RB_0LD1LB_1LE1LD_1LA1RF_1LD1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1759: ~halts (TM_from_str "1RB1RF_0LC---_1LD1LC_1LE0LF_1RA1RE_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1760: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_0LF---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1761: ~halts (TM_from_str "1RB0RB_1LC1RF_---1LD_0RE0LD_1RA1RE_1LE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1762: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0RA_0RB0LD_1RF1RE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1763: ~halts (TM_from_str "1RB1LB_1RC0LD_1LC1RA_---0LE_0RA0LF_0LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1764: ~halts (TM_from_str "1RB1RA_1LC0RF_0LD1RC_0LA0LE_1LA1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1765: ~halts (TM_from_str "1RB1RE_1LB1RC_1RA1LD_---0LE_0RA0LF_0LD0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1766: ~halts (TM_from_str "1RB0LE_1LC0RD_0LA1RB_0RB0LD_0LF1RB_0LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1767: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA1RB_0LD1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1768: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0LE_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1769: ~halts (TM_from_str "1RB1RA_1LC1LB_0LF0LD_0RE0LC_0RA---_1RD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1770: ~halts (TM_from_str "1RB1LE_1LC1RA_0RF1LD_1RD0RB_0LC0LE_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1771: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LE_1RE1RD_1LF1LC_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1772: ~halts (TM_from_str "1RB1LF_1LC1RE_1LD1LC_0RB0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1773: ~halts (TM_from_str "1RB1RE_1RC1LF_1LD1RA_0RE0LD_0RF---_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1774: ~halts (TM_from_str "1RB1RE_1RC1LD_1LD1LF_0LD0LA_0RF---_0RE0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1775: ~halts (TM_from_str "1RB1RE_0LC0LD_1RA1LB_0LF1LA_1RC0RE_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1776: ~halts (TM_from_str "1RB1LD_0RC1RF_1LC0LA_---0LE_0RB1LE_0RF0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1777: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB1RC_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1778: ~halts (TM_from_str "1RB1LA_0RC1RF_1RD1LA_1LE---_0RB0LE_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1779: ~halts (TM_from_str "1RB1LD_0LC0RB_0LD1LC_1LE1LA_1LF---_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1780: ~halts (TM_from_str "1RB0LC_1RC1RE_1LD0LA_1LA0RD_1RF---_1RD1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1781: ~halts (TM_from_str "1RB1LD_0LC1RF_0LD1LB_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1782: ~halts (TM_from_str "1RB---_0RC0RF_1LD1RE_1RC1LB_1RC0RA_0LF0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1783: ~halts (TM_from_str "1RB1RC_1LA1LD_0RB0RC_0LF0LE_0LA1RB_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1784: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_0RE1LE_1RA1RF_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1785: ~halts (TM_from_str "1RB---_0RC1LC_1LA0RD_1RE1RD_1LF1LE_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1786: ~halts (TM_from_str "1RB1LE_1LC1RA_1RD0LC_0RA---_0LF0LE_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1787: ~halts (TM_from_str "1RB1LD_1LC0RE_1LE0RA_1LA1RB_1RF0RB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1788: ~halts (TM_from_str "1RB1LF_1LC0RB_1LD0LC_1RE0RD_---0LA_1LA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1789: ~halts (TM_from_str "1RB---_0RC0LC_0RD0LC_1RE1RD_1LF1LE_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1790: ~halts (TM_from_str "1RB---_1LC0RC_0LD1RC_1RA0LE_0RA1LF_0LB1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1791: ~halts (TM_from_str "1RB1RA_1RC0LF_1LD0RE_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1792: ~halts (TM_from_str "1RB1RA_1LC1LF_0RA0LD_0RB0RE_0LC0LF_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1793: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD1LC_0RE0LD_1RF---_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1794: ~halts (TM_from_str "1RB0RF_0LC0LF_1RF1LD_0LE1RF_1LC---_0RF0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1795: ~halts (TM_from_str "1RB0LD_0RC---_1LD1RA_0LE1RF_0RA0LE_1RC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1796: ~halts (TM_from_str "1RB---_0RC1RE_1LD1LF_0RB0LD_1RC1RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1797: ~halts (TM_from_str "1RB1RA_1LB0LC_1LD1LC_1LE0RA_1RF---_0LA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1798: ~halts (TM_from_str "1RB1RF_1RC---_1LD0RE_0RA0LD_1RA1LE_1RE1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1799: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA1RB_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1800: ~halts (TM_from_str "1RB1LF_1LC1LE_0RD0LC_1RE---_0RA1RA_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1801: ~halts (TM_from_str "1RB1LE_1LC1LF_---0LD_0RE0LC_1RF0LE_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1802: ~halts (TM_from_str "1RB1LD_1LC0RB_1LE0RA_1LA1RE_1RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1803: ~halts (TM_from_str "1RB---_1LC1LD_1RF1LA_1LE0LE_1LB1RE_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1804: ~halts (TM_from_str "1RB1LB_0RC1LA_1RD1RC_1RE0RE_1LF---_0RB0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1805: ~halts (TM_from_str "1RB1LA_0RC1LF_1RD0LE_1LE---_0RA0LC_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1806: ~halts (TM_from_str "1RB0RE_0LC1LD_1RA1LB_0RA1LB_---1RF_0RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1807: ~halts (TM_from_str "1RB1RE_1RC1LC_1LD1LC_0RE0LD_0RB1RF_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1808: ~halts (TM_from_str "1RB1RA_1RC1LE_1LD0RB_0RC0LD_1RA1LF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1809: ~halts (TM_from_str "1RB0LE_0RC---_0RD0LC_1LE0RF_0LA1RB_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1810: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD---_1LE1RF_1LA1LD_1LE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1811: ~halts (TM_from_str "1RB1RA_0LC0RB_1LE1LD_0LB---_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1812: ~halts (TM_from_str "1RB1RA_0RC0RD_1LD---_0LE0RE_0LF0RE_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1813: ~halts (TM_from_str "1RB1RA_1LC1LF_0RD0LC_0RE---_1RA1RC_1LE1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1814: ~halts (TM_from_str "1RB1LD_1RC1RD_1LA0LA_1LF0RE_0LF0RD_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1815: ~halts (TM_from_str "1RB1RE_0LC0LA_1LF1LD_1LA1RE_0RB0RE_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1816: ~halts (TM_from_str "1RB1RA_1RC0LF_1LD0RA_1RE0LD_0RA---_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1817: ~halts (TM_from_str "1RB1LE_0RC1RA_1LD1LA_0RA0LE_0LF0RA_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1818: ~halts (TM_from_str "1RB0LD_1RC1LB_1RD1RA_1LE1RF_0RD0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1819: ~halts (TM_from_str "1RB1LD_1LC0RB_1LE1LD_1LA1RE_1RF0RE_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1820: ~halts (TM_from_str "1RB1LB_1LC0LC_1LA1RD_0RE0RD_0LC0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1821: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LB_1LE1LD_1LA1RE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1822: ~halts (TM_from_str "1RB1RA_1LC1RE_1LD1LC_1LA0LE_0LF0RE_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1823: ~halts (TM_from_str "1RB1LE_0LC0RB_0LD1LB_1LA1RD_1LF0LD_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1824: ~halts (TM_from_str "1RB1RF_1LC1LB_0RD0LC_1RE1RA_0RB1RD_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1825: ~halts (TM_from_str "1RB---_0RC0LB_0RD1LA_0RE1RD_1RF1LE_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1826: ~halts (TM_from_str "1RB1RA_1RC1RF_1LD0RB_0RE0LD_1RA1LE_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1827: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA1RB_---0RE_0LA0RF_0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1828: ~halts (TM_from_str "1RB1RC_1LA1LE_0RF0RD_0RB1LA_0LA0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1829: ~halts (TM_from_str "1RB1RA_1RC0RB_1LD0RF_0LE0LD_1LA1LE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1830: ~halts (TM_from_str "1RB1LE_1LC1RA_1RD0LC_0RA1RB_1LF0LE_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1831: ~halts (TM_from_str "1RB1RA_1LC0RB_1RC0RD_---1RE_0LF1LF_1LA1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1832: ~halts (TM_from_str "1RB1RF_0LC0RD_1LE1LA_0LE0LA_1LC---_0RB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1833: ~halts (TM_from_str "1RB1LE_1LC1RA_---0LD_0RA0RD_0LF0LE_1RD0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1834: ~halts (TM_from_str "1RB1LF_0LC1RD_1LA1LD_0LE0RD_0LF---_1LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1835: ~halts (TM_from_str "1RB1LD_1LC0RD_0RA0LC_1RE1RD_1RF---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1836: ~halts (TM_from_str "1RB1RA_0LC---_1LD1LC_0LE0RA_1RE1LF_0LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1837: ~halts (TM_from_str "1RB0LE_0RC---_0RD1LE_1LE0RF_0LA0RE_0RB1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1838: ~halts (TM_from_str "1RB1RE_1LC0RD_---1LA_1RA1RD_1LF0LC_1LB1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1839: ~halts (TM_from_str "1RB1LD_0RC0LD_1LD1RA_0LE0LF_0RA0LE_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1840: ~halts (TM_from_str "1RB0LF_0RC0LB_0RD---_1RE1LD_1LB1RF_1RD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1841: ~halts (TM_from_str "1RB---_1LC0LF_---0RD_1LF1RE_1RD1LF_1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1842: ~halts (TM_from_str "1RB1LA_1RC1RB_0RD0LA_1LD1RE_0RF0LE_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1843: ~halts (TM_from_str "1RB0RC_0RC0LA_1LD0RE_0LA0LB_1LF1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1844: ~halts (TM_from_str "1RB1LE_1LC1RA_1RF1LD_1RD0RB_0LC0LE_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1845: ~halts (TM_from_str "1RB1LF_0LC0RB_0LD1LC_1LE1LD_1LA1RE_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1846: ~halts (TM_from_str "1RB1RE_1LC0RD_0RA0LC_1RE---_1RF1RE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1847: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD1LD_0LE1RF_1RA---_1LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1848: ~halts (TM_from_str "1RB1LA_1RC0RD_0LA1RD_0LA0LE_0RB1LF_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1849: ~halts (TM_from_str "1RB1LC_1LC1RC_1LE0RD_0LE0RC_1LF---_1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1850: ~halts (TM_from_str "1RB0LC_1LA1RB_0LD0LD_1RE1LD_0RB0RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1851: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1RF_1LA---_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1852: ~halts (TM_from_str "1RB1LA_1RC1RB_1LD1LC_0RE0LD_1RF---_1LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1853: ~halts (TM_from_str "1RB1RE_0RC1RF_1LD1LC_0RA0LD_1RC---_1RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1854: ~halts (TM_from_str "1RB1RD_1RC---_0RD1LE_1RE1RA_1LF1LC_0RE0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1855: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LC_1RE1LA_1LF0RC_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1856: ~halts (TM_from_str "1RB0LE_0RC1LC_1RD1RC_1LA1LF_0RB0LE_---1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1857: ~halts (TM_from_str "1RB1LA_1LC0RB_0LD1RA_0LE---_1LF0RA_1LD1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1858: ~halts (TM_from_str "1RB0RE_1RC0RA_0LD0LF_1RA0RE_1LF---_0LC0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1859: ~halts (TM_from_str "1RB1RA_1LC1LB_1RA0LD_1RE1LE_0RF1RC_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1860: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RE_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1861: ~halts (TM_from_str "1RB0LE_0RC1LA_1LD0RF_0RB---_0LA1RB_0RD0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1862: ~halts (TM_from_str "1RB1LA_1LC1LD_1RD0LC_0RA1LE_---0RF_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1863: ~halts (TM_from_str "1RB1LD_1LC0RB_0LD0LB_1LA1RE_0RF0RD_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1864: ~halts (TM_from_str "1RB1RA_0RC0RB_1LD0LC_0LE---_1LF0LC_1LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1865: ~halts (TM_from_str "1RB1RA_1RC0LF_1RD---_1LE0RA_0RC0LE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1866: ~halts (TM_from_str "1RB1RA_1LC1LF_1LD0LC_1RE0LE_---0RF_0RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1867: ~halts (TM_from_str "1RB---_1RC1RB_1RD1LC_1RE1LB_1LF0RA_0RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1868: ~halts (TM_from_str "1RB1RE_0RC1LA_1LD1LC_0RA0LD_1RC1RF_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1869: ~halts (TM_from_str "1RB0LA_1RC---_0RD1RD_1RE0RB_1LF1LA_1LC0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1870: ~halts (TM_from_str "1RB0LA_1RC1RD_0RD1RF_1LE1LA_0RB0LE_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1871: ~halts (TM_from_str "1RB---_1RC1LD_1RD1LC_1LE0RF_0RD0LE_1RA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1872: ~halts (TM_from_str "1RB0LD_1RC1RF_0LA1RA_---1LE_0LF1LA_0RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1873: ~halts (TM_from_str "1RB0RC_1RC1LF_1LD0RB_0LE1RA_---0LD_0LB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1874: ~halts (TM_from_str "1RB1LD_1LC1RF_1RF0LD_1LE0RD_1LA---_0LC0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1875: ~halts (TM_from_str "1RB0LD_0RC1RE_1LC0LA_0LF1LA_0RA0LC_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1876: ~halts (TM_from_str "1RB0RD_1RC1RB_1LD1LC_0RE0LD_0RF1LA_1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1877: ~halts (TM_from_str "1RB1RD_0LC1LC_0RF1LD_1RE0LB_0RA1RA_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1878: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD0RA_1RE0LD_0RA---_1LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1879: ~halts (TM_from_str "1RB1RA_1RC---_1RD1LF_1LE0RB_0RD0LE_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1880: ~halts (TM_from_str "1RB0LE_1RC0RF_1RD1LA_1LA0RB_0LF1LB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1881: ~halts (TM_from_str "1RB---_1LC1LF_0RD0LC_1RE1RA_0RB0RF_1RD0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1882: ~halts (TM_from_str "1RB1RA_0LC0RB_1LD1LC_0LE1LE_1LA0RF_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1883: ~halts (TM_from_str "1RB0LF_0RC1LD_1LD0RB_0LE---_0LA1RB_0LD1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1884: ~halts (TM_from_str "1RB1LE_1RC---_1RD1LE_1LD1RA_0LE0LF_0RA0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1885: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD---_0LE1RE_1RA0LD_0LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1886: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE1RA_1RF0RE_1LA---") c0.
Proof. solve_loop1'' 22 0 1 4000%N. Time Qed.

Lemma tm1887: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE1RA_1RF0RE_1RA---") c0.
Proof. solve_loop1'' 22 0 1 4000%N. Time Qed.

Lemma tm1888: ~halts (TM_from_str "1RB1RA_1LC1LB_0RD0LC_1RE1RA_1RF0RE_1LD---") c0.
Proof. solve_loop1'' 22 0 1 4000%N. Time Qed.

Lemma tm1889: ~halts (TM_from_str "1RB1LE_1LC0RD_1LF1LA_---1RE_0LF1RB_0RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1890: ~halts (TM_from_str "1RB1LF_0RC1LC_1LD0RE_1LB1LA_---1RF_0LB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1891: ~halts (TM_from_str "1RB1LA_0LC1RE_1RA1LD_1RA0LF_1RD0RB_---1LC") c0.
Proof. solve_loop1_0 4000%N. Time Qed.

Lemma tm1892: ~halts (TM_from_str "1RB1RF_1RC1RD_1RD---_1LE0RA_0RC1LF_1RA0LE") c0.
Proof. solve_loop1'' 20 0 1 2000%N. Time Qed.

Lemma tm1893: ~halts (TM_from_str "1RB---_1LC0RE_0RA1LD_1RE0LC_1RF1RD_1RA1RB") c0.
Proof. solve_loop1'' 20 0 1 2000%N. Time Qed.

Lemma tm1894: ~halts (TM_from_str "1RB1RC_1RC---_1LD0RF_0RB1LE_1RF0LD_1RA1RE") c0.
Proof. solve_loop1'' 20 0 1 2000%N. Time Qed.

Lemma tm1895: ~halts (TM_from_str "1RB0LF_1RC1RA_1RD1RE_1RE---_1LF0RB_0RD1LA") c0.
Proof. solve_loop1'' 20 0 1 2000%N. Time Qed.

Lemma tm1896: ~halts (TM_from_str "1RB---_0RC0RA_1RD0RF_1LE0LD_1RC1LC_1RA1LC") c0.
Proof. solve_loop1_0 8000%N. Time Qed.

Lemma tm1897: ~halts (TM_from_str "1RB0RA_1LC1RC_1LA0LD_1LE1RC_1LF---_0LC0LE") c0.
Proof. solve_loop1_0 8000%N. Time Qed.

Lemma tm1898: ~halts (TM_from_str "1RB1LD_1RC---_0RD0RB_1RE0RA_1LF0LE_1RD1LD") c0.
Proof. solve_loop1_0 8000%N. Time Qed.

Lemma tm1899: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LC0LA_1LF1RB_0LC---") c0.
Proof. solve_loop1_0 8000%N. Time Qed.

Lemma tm1900: ~halts (TM_from_str "1RB1RD_0LC1RF_0RE1LD_1RA0LC_1RE0RA_1LC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1901: ~halts (TM_from_str "1RB---_0LC1RF_1LC0LD_1LE1LF_1RD1LA_1LD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm1902: ~halts (TM_from_str "1RB0LF_1RC1RA_1RD1RE_1RE---_1LF0RB_0RD1LA") c0.
Proof. solve_loop1''' 24 10 0 1 8000%N. Time Qed.

Lemma tm1903: ~halts (TM_from_str "1RB1RC_1RC0RB_0LD1RE_0LE1LD_1RF0RC_1RA---") c0.
Proof. solve_loop1'' 20 0 1 8000%N. Time Qed.


