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
Ltac solve_loop1 := solve_loop1_0 2000%N.

Close Scope sym.

(* these were solved by a weaker version of RRBA(loop1) that only keep track of record-breaking in one direction, they should also be CTLable; now we use RRBA(loop1) for them *)

Lemma tm1: ~halts (TM_from_str "1RB1LC_1RC0RE_1LD0RB_0RB0LE_1LA1LF_0LC---") c0.
Proof. solve_loop1_0 10000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RD_1LC0RA_1RE0LD_1LE1LF_1RA1LB_0LB---") c0.
Proof. solve_loop1_0 10000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RE_0RC0LD_1LD1RA_1RE1LD_1LF1RC_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0RE_0RC---_1LD1RC_1LE1LF_0RC0LD_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LA_1RC1RD_1LA1RF_1LF1RE_0LB0RB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0LC_1LA0RF_1RD1LA_0RE1RA_0LE1LC_0RE---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB0LB_1LA1LC_0LE0RD_1RD1RA_0RD0LF_1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB1LA_1RC1RD_0LA0RF_1RE0RB_1LE0LF_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0LF_0RA1LE_0LC---_1LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0LD_0LB1RC_1LA0RE_1RE1LD_1RF1RB_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1RF_1LC0LD_1RE1LD_1RE0LB_1RA0RE_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1LA_1RC1RD_0LA0RF_1RE0RB_1LE1LC_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RF_0LE0RA_1RA1LF_0LB0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB1LC_1LA0RF_1LD0LA_1RE0RD_---0RB_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0RD_0RC---_1LD1RC_0RC1LE_0LD0LF_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LD_1RC---_1LD1RE_0LA1LD_1RA0RF_1LD0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB0LC_1LA0RD_0RB1LE_1LC1RD_1LF1LA_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB0RF_1RC0LE_1RD---_1LE1RA_0LB1LE_1LE0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RA_0LC0LD_1RA1LB_1RF1LE_1LC1LD_---0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0RF_1RC0LB_1LD0RE_0RD1LB_1LA1RA_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0LE_0LC0RC_1RF1RD_1LA0LF_1RC1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB0LC_1LA0RD_0RB1LE_1LC1RD_1LF0RF_---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0RC_1LA0RE_1RE0LD_1LB---_0LF1RF_0RA1LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0LC_1LA1RF_1RD1LC_1RE1RB_---1RA_1LA0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0LF_1LC0RB_1LD1LA_0LC1LE_1RE1RA_---0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB1RD_1LB0LC_1RA1LC_0RE0RA_0RF0LF_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB---_1LC0LF_0LB0RD_1RA1RE_0RB1RC_1RD1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB0RB_0RC0LD_1LD1RC_1LB1LE_0LA1LF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB0RE_1LB1LC_0LD0RF_1RE1LD_1RC1RA_---0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB1LE_1RC1LC_0LD1RE_---1LA_1RF0LA_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB1LA_0RC1RE_1LD0LD_0LA1RF_0RB0RD_---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB1LC_1LA---_1RD0LC_1RF1RE_1RA1LF_0RD0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0RF_1RE0RD_---0RB_0LA1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB---_0RC0LC_0LD0RF_1LE0RF_1LC0LA_0RB1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0LC_1LA1RF_1RD1LC_1RE1RB_---1RA_0LD0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB0RB_0LC1RA_0LD1LC_1RA1LE_1LF0LF_---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB0LF_1LC0RB_1LD1LA_0LC1LE_1RE0RF_---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB0LE_0LC0RC_1RF1RD_1LA1RB_1RC1LE_---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1LF_1RC---_0RD0LE_1LE1RF_0LA0RB_0LC0RE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB1LD_1LC1RB_1RE1LA_1LF0LC_0RF---_0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0RE_0LC1LD_1RD0LD_1RE1LB_1RF1RA_0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB1LA_1RC1RD_1LA1RF_1LF1RE_1LF0RB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB1LC_1LA0RE_1LD0LA_1LB0RD_---0RF_1LA1RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB1LD_0RC1RD_0LC1LA_1RE0LA_1LD0RF_0RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB---_1RC1RD_1LB0RB_0RF0LE_1LE1LC_0LE0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1LA_0RC1RE_0LD0LA_1LC0RB_1RF1RD_---1RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB---_1RC0RB_1LD0RC_1LF0RE_0LA1LB_0LD0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1LA_1RC1RD_1LA1RF_0LD1RE_1LF0RB_---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB---_1RC0LD_1LB0LF_0RE1LE_0LC1RA_1LD0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB0LC_1LA0RD_1RD1LC_1RE1RF_---1RA_0LF1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB1LC_1LA1RF_1LD0LA_1RE0RD_---0RB_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1LA_0RC1RE_0RD0LD_0LE---_1LF0RB_0LF1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RF_1RC0LB_1LD0RE_1RC1LB_1LA1RA_---0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0RD_0RC---_0LD0LF_0RE1LC_1LD1RE_0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1LD_1RC1RF_0LD---_0LE1LA_1RA0LA_1RD0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB1LB_0RC0RB_0RD0LE_1LE1RB_0LF---_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0RB_0RC1LD_1LB1RC_0LB0LE_0LA1LF_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB1LD_0RC1RD_1LC1RA_0LE0LA_---0LF_1LB0RF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB1LA_0LB1RC_1RD0RE_0LA---_0RF1RF_1LB0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB1LE_0RC---_1RD0RB_1LE1RE_0LF0LE_0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB1LA_0RC1RD_0RD---_1LE0RE_0LE1RF_1LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB1LE_0RC1RB_1LD0RB_1LA---_1LC0LF_1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0LC_1LA0RE_1RD1LA_1RD1RA_0RF---_0LF1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB1LB_1LC0RE_0RD0LD_1LA1RF_1LD1RB_---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB0LE_0RC1RB_1LD0RB_1LE---_1RB1LF_1LC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB0RC_1LA0RE_1RE0LD_1LB1LD_0LD1RF_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB0RF_1LC1RC_0LD0LC_0LE0RF_1RF1LC_0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB---_0RC0RB_1LD1RC_0RE1LF_0LA1LB_0LE0LD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB0LB_1RC1LE_1RD1RF_0LE---_0LA1LB_1RE0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB0LC_1LA0RD_1RD1LC_1RE1RF_---1RA_1LA0LE") c0.
Proof. solve_loop1. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_0RD1RE_1LF1RB_0LD1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0RF_1LC0RC_0LD1RD_0RA0LE_1LE1LB_1RC---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_0RD1RE_1LF1RB_1LF1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB1LA_1RC0RF_1RD0RB_1RE1LC_1LF---_0LF0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB1RE_1LC1RD_---0LD_1RA1LD_0LF0RA_0LC1LF") c0.
Proof. solve_loop1. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RF_---0RB_1RF0RD") c0.
Proof. solve_loop1. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB0LC_1LA0RD_1RD1LC_1RE1RF_---1RA_1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0RB_0RC1LF_1LD1RC_1LE1LB_0LA0LD_---0RE") c0.
Proof. solve_loop1. Time Qed.

