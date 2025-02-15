From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMAddOneSymbol.
Module BB62' := TMAddOneSymbolCtx BB62.
Module RRBA62 := RRBA BB62'.
Module BB62'spec := TMAddOneSymbol BB62.
Require Import NArith.
Require Import String.


Ltac solve_loop1'' min_b n_skip k T :=
  rewrite halts_halts';
  apply BB62'spec.from_nonhalt;
  rewrite <-RRBA62.TM.halts_halts';
  apply (RRBA62.decide_loop1_spec' _ (min_b,8%nat) n_skip k T).
Ltac solve_loop1' n_skip k T := solve_loop1'' 8 n_skip k T.
Ltac solve_loop1_0 T := solve_loop1' 1%nat O T; native_cast_no_check (eq_refl true).
Ltac solve_loop1 := solve_loop1_0 1000%N.

Close Scope sym.


Lemma tm1: ~halts (TM_from_str "1RB0LB_0RC1LF_1LB1RD_1LE1RC_0RD1LA_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1RF_0RC0RD_1LA1LC_0LE0RE_0LC0RB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1LE0RD_0RE1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RD_---0RF_1LF1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LC_1LA1RF_1LD0LA_1RE0RD_---0RB_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB1LC_1LC1RA_0LE0LD_0RA1RD_---0LC_------") c0.
Proof. solve_loop1. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1LC_1LA1LF_1LD0LA_1RE0RD_---0RF_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1RD_1LA1LD_---1RF_0RD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB1RD_0RC0LB_0RD---_1RE1RF_1RF1LE_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB1RD_0LC1RB_1RA1LC_1RE0RA_1LF0LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LF_1RE0RD_---0RB_1RB1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1RE_1LC1RA_1LC0LD_0RE1LA_1RF1LC_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB1RD_0LC1RE_0RE1LD_1RA0LC_1LC1RF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0RE_1RC0LA_0LC1RD_1LB1RF_1LD0RC_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0RE_0LC0RA_1LD1LC_1RA1RF_0LB0RB_---1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB1LB_1RC0LA_1LD1RB_0RA0LE_---0LF_0RD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD0RE_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE---_1RA1RE_1RC1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB0RB_0LC1RE_1LD1LC_1RD1LA_---0RF_0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB1LC_0LC1RC_1RD0RD_0LE1RF_1LA1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1RD_1LA1LD_---1RF_1RC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RE_0LC---_1RD1LC_0LD1RA_0RF1RF_1LD0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1LA_0LA1RC_1LB0RD_0LE1RF_1RD1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB1LC_0LC1RD_1RE1LA_0RB0RE_0LA1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB1LD_1LC1RB_1LB1LD_1LE0LA_1RF0RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB1LB_1RC0LA_1LD1RB_---0LE_0RF0LF_0RB0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB1RD_0LC1RC_1LD1LC_1RE1RF_0LB0RE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0RB_0LC1RE_1LD1LC_0RB1LA_---0RF_0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD0LD_0LA1RF_1RB0RD_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1LE0RD_0RF0RB_---1RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB1LE_1LC1RE_0RD0LC_0RB1RA_1RF0LE_1RD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_0RB1RA_0LB1LF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB1RA_1LC1LF_1RA0LD_0RE0LE_0RA0LC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LE0LA_1RB1LA_---0RE") c0.
Proof. solve_loop1_0 4000%N. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB1LB_1LC0RD_1RD1LA_---1RE_0LF1RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB0LC_0LC1RF_---1LD_0RE1LA_0RF1RE_1LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB1LD_1LB1RC_1RB1LD_0LF0LE_0RA1RE_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RF_---0RB_1RE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA1LF_0RE0LE_0RB0LA_---1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB0RD_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB1LA_0LC1RF_1RD1LC_0LA1RE_1LD0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB1RD_0LC1LC_1RA1LC_1RE0RA_1LF0LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB1RD_0RC0LB_0RD---_1RE1LF_1RF1LE_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE1RF_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1LD_1LC0RD_---1LA_1LB0LE_1RA0LF_0RF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB0RB_0RC0LF_1LD1RC_1LE1LB_0LA0LD_---1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB0LF_1LC1RA_---0LD_0RE0LE_0RA0LC_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LC1RE_1RD0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB1LD_0LC1RC_1LA1RC_1LE0LA_1RF0RE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB0RF_0LC---_1LD1LC_0LE0RA_1RE1RF_0LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB0RF_0LC1RF_1LD1LC_0LE0RA_1RA---_0LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB1LE_1LC1RA_0LF0LD_0RA1RD_0LF0LD_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB1RD_0LB1LC_1RA1LC_1RE0RA_1LF0LE_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1LC_1LC1RE_0LF0LD_0RA1RD_1RB1LC_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB1LA_1RC1RC_0LD0RE_1RE1LD_---1RF_0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1LC_1LA1RB_0RD0LA_1LE1LD_1RF0RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0RF_---0RE_0LB0RB_1LC1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LE1RE_1LA0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB1LB_1LC0RD_0RD1LA_---1RE_0LF1RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_0RA1LA_---1LF_0LA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD0LD_0LA1RF_0RB0RD_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB1LD_0LC0RE_1LD1RD_1LA0RC_---0RF_0LB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LD1RE_1LA0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1RE_0LC0RB_0LA1LD_1LA1LD_0RA1RF_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB1RD_1RC1LB_1LD1LF_0RE0LD_0RF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LC1RE_1LB0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB0RD_0RC1RA_1LD0LD_0LE1RF_1RB1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RF_---0RB_1RE0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB---_0LC1RF_1LC0LD_1LE1LF_0RB1LA_1LD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE1LF_---0RB_0RF0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB0LE_0LC---_1RF0RD_1LE1RC_1RD1LE_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB1RE_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD0LD_0LA1RF_1LD0RD_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RD_---0RF_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB1LB_1RC0LA_1LD1RB_0RC0LE_---0LF_0RD0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB1LA_0LA1RC_1LD0RE_1RE1LD_0LC1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB0LC_0LC---_1RD1LC_1LC1RE_1RF0RD_1LA0LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB1LD_0LB1RC_1LA1RC_1LE0LA_1RF0RE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_0RA1LA_---1LF_1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB1LC_1LA1LE_1RD---_0LF1RE_1LB0RD_1LF0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB1LE_0LC1RC_1LE0RD_0LE1RF_1RD1LA_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB0RB_0RC1LD_1LB1RC_1RE0LE_0LA1LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB1LA_0LC1RF_1RD1LC_0LA1RE_1LA0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB1LF_0LC0RA_1RE1LD_1LE---_1RA0RC_0LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_0RA1LA_---1LF_1RD1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB1LB_1LC0RD_1RA1LA_---1RE_0LF1RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB1RD_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB1LA_1LC1RF_0RD0LC_0RE---_1RA1RE_1RC1LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB1LC_1LA1RF_1RD1LA_---1RE_0LC0RB_0LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB0LC_1LC0RA_1LA1LD_0LE---_0RE0RF_1RE1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB1RC_1LA1RF_1RA0LD_0RE1LC_1RE0RA_1LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1RD_1LA1LD_---1RF_1LC1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB1RA_1LC1LF_0LA0LD_0RE0LE_0RA0LC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB1LA_1RC0LF_1RD1LF_1LE0RB_0RD0LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB1LA_0LC1RF_1RD1LC_0LA1RE_0RB0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB1RA_1RC0LF_1LD0RD_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0RB_0RC1LD_1LB1RC_1LA0LE_0LA1LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB1RE_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE1LE_0RF0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0LD_1LC1RB_0RC1LA_0LF1LE_1RC0LC_0LE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB1RD_0RC0LB_0RD---_1RE1RD_1RF1LE_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB1LC_1LA1RF_1LD0LA_1RE0RD_---0RB_0LF1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB1LC_1RC1RB_1LD1LF_0RE0LD_0RB1LB_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RD_---0RB_------") c0.
Proof. solve_loop1. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB1RA_1LC1RD_0RD1LD_1LE0LE_0RA1LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB1LC_0LC1RD_1RE1LA_1RE0RE_0LA1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1RF_1RC0RE_0LD0RB_1LA1LD_0LC0RC_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LC1RE_1LA0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LC1RE_0RD0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB1LD_1LC0RD_0RF1LA_1LB0LE_1RA0LC_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB1RA_1LC1LE_0RB0LD_0RE0LC_0RA1LF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB1RD_0LC0RE_1RB1LD_1LC0RA_---0RF_0LB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB1LA_0LC1RF_1RD1LC_0LA1RE_0RB0LD_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_0RE0RD_1RF1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB0RE_1LC1RE_0LD1LB_1RD0RA_0LF0RB_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB---_1LC1RB_1RB1LD_1LE0LC_1RF0RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB0RB_1RC1RA_0LD0LF_---0LE_1LD1LF_1LB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB0RB_0RC0LD_1LD1RC_1LB1LE_0LA0LF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB1RA_1LC1LF_1LE0LD_0RE0LE_0RA0LC_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB0RB_0LC1RE_1LD1LC_0RB1LA_---0RF_0LF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB1LC_0LC1RD_1RE1LA_0RB0RE_0LA1RF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB0LE_1RC1RB_0RD0LA_1LD1LE_0RF1LA_0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB0RB_0LC1RE_1LD1LC_1RD1LA_---0RF_0LF1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB1LC_0LC1RD_1RE1LA_1LC0RE_0LA1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB1RC_0LA0RE_0LD1RF_1LA1LD_0LC0RB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB0LB_0RC1LF_1LD1RE_0RE1LA_1LB1RC_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB1LA_0LA1RC_1RD0RD_0LE1RF_1RD1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB1LC_1LB1RA_0LE0LD_0RA1RD_---0LC_------") c0.
Proof. solve_loop1. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB0RE_1LC0RA_1RB1LD_0LB0LF_1RA1RC_0LD---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB1LA_0LA1RC_0RD0LB_0LE1RF_1RD1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB0RD_0RC1LD_1LB1RC_1RE0LE_0LA1LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB1RC_1LA1RE_1RA0LD_0RE1LC_1LD1RF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB1LA_0LA1RC_0RD0RD_0LE1RF_1RD1LE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB1LC_1LA1LE_1RD1LF_0LC1RE_1LB0RD_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB1LD_0RC0LB_0RD---_1RE1RD_1RF1LE_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB1LD_0LC1LC_1LA1RC_1LE0LA_1RF0RE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB1LC_1LA1RF_1LD0LA_1RE0RD_---0RB_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB1LA_1RC0LF_1RD1LA_1LE0RB_0RD0LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB0LE_1RC---_1RD0RF_1LA0LD_1RF1LE_1LE1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB0RB_0RC1LD_1LB1RC_0LB0LE_0LA1LF_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RF_0RF0LE_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB0RF_1LC1LE_0RA0RD_---1RE_1LB0LB_1RA1RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB1LA_0LA1RC_1LD0RE_1RE1LD_0LD1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB0RE_0LC1RA_0LD1LC_1RA0RD_0LB1RF_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB1LC_1LA0LF_1LD0LA_1RE0RD_---0RB_0RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB1LD_1RC1RF_0LD0RB_1RE1LA_---1RC_0LA0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB1LE_1LC0RA_1RA0RD_1RF1LB_0LA0LC_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB1RA_1LC1LE_0RD0LC_0RA1LA_---1LF_1LD1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RD_---0LF_0RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB0LF_1LC1RA_0RD0LD_0RA0LE_---0LC_1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB1LC_0LA1RF_1RD1LA_0LC1RE_0RD0RB_---0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB1LF_1LC0RD_0RC1LA_1LB0LE_1RA0LC_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB1RE_0LC0RB_0LD1RD_1LA1LD_---1RF_1LD1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB1LA_1RC1RB_1RD1LA_1LE0RF_0RD0LE_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB1LC_0LC1RD_1RE1LA_1LE0RE_0LA1RF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB1LC_1LB1RA_0LE0LD_0RA1RD_---0LF_0LE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB1LA_0LC1RF_1RD1LC_0LA1RE_1RD0RB_---0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB---_1LC0LF_1LE1RD_0RC0RB_0RF0LC_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_0RE0RD_---1LF_1RF0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB0LC_1LC0LE_1LA1RD_0RC0RB_1LF1RA_---0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB1RD_0RC0LB_0RD---_1RE0RE_1RF1LE_1LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB1LF_1LC1RB_---1LD_0LE0LA_1RF0RF_0RB0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB1LD_1LC1RB_1RB1LD_1LE0LA_1RF0RE_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB1LC_1LC1RA_0LE0LD_0RA1RD_---0LF_0LE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB0LD_1LC1RC_1LA1RA_---1LE_0RF1LA_0RC1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB1RD_1RC1LB_1LD1RF_0RE0LD_0RF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0RF_---0RE_0LB0RB_1RB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB1RF_1LC0RD_1LA1LC_0LE0RE_0LC0RB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB1LB_1RC0LA_1LD1RB_---0LE_0RF0LF_0RA0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0RF_---0RE_0LB0RB_0RB1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB1RE_1RC1LB_1LD1LF_0RE0LD_0RF---_1RA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB1RA_1LC1RD_0RC1LD_1LE0LE_0RA1LF_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB1RA_1RC1LF_1LD1RE_0RE0LD_0RB---_1RA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB1LA_1LC1RF_1RD1LC_---1RE_0LA0RB_0LC0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB1LC_1LA1RF_1LD0LA_1RE0RD_---0RF_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB1LB_1LC0RD_0RB1LA_---1RE_0LF1RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

