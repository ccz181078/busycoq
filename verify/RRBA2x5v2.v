From BusyCoq Require Import Individual25.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMAddOneSymbol.
Module BB25' := TMAddOneSymbolCtx BB25.
Module RRBA25 := RRBA BB25'.
Module BB25'spec := TMAddOneSymbol BB25.
Require Import NArith.
Require Import String.


Ltac solve_loop1'' min_b n_skip k T :=
  rewrite halts_halts';
  apply BB25'spec.from_nonhalt;
  rewrite <-RRBA25.TM.halts_halts';
  apply (RRBA25.decide_loop1_spec' _ (min_b,8%nat) n_skip k T).
Ltac solve_loop1' n_skip k T := solve_loop1'' 8 n_skip k T.
Ltac solve_loop1_T T := solve_loop1' 1%nat O T; native_cast_no_check (eq_refl true).
Ltac solve_loop1 := solve_loop1_T 1000%N.

Lemma tm1: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA1RA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB2RB4RB1LB1RB_1LA3RB2RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA1RB4LA2RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB2RA1LA2RB---_2LB3RB4LB1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB2RB3RB0RB3LB_1LA3LA---4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB3LA3LB0RB---_2LA3LA4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB2RB3LA0RB3LA_0LB1LA0LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB2LA3RB0RB2LB_0LB2LA1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB3LA0LA4RB0RB_0LB2LA1RA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA3LA2LB0RA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB2RA3LA2RB2LA_2LA4LB1LA1RA---") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1RA3RB0LA3RA_2LA3RA2LB4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB3RB4RA4LA0RB_2LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA3LA2LB2RA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB3RA3LB4LA3RB_2LA---0LB3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB3RB1LB0RB---_2LA2RB4LA---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB2RB4RB4LB1RB_2LA---3RB0LA3RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB4LA4LA1LA3LA_2LB3RA---0RB0RA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB3RA3RB1LA---_2LA2RB3LA4LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB3RB4LA4LA0RB_2LA---2LB3LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB3RB2LA4LA0RB_1LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB3LA2RA---2LB_2LA2RB4RB1LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB2RB4RA0LB---_2LB3RB1LB1LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB2LA3RA4LB1LA_0LA0RB1RA2LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB3RA---4RB1LA_2LB3RB4LB1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB3RB1RB4LA2RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB4LA---4LA0RB_2LB3RB3LA0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB2RB4RB0LB1RB_2LB1RB3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB4RA3RB4RB1LA_0LB2RB3LA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB3RA2RB4LA3RB_2LA---0LB3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB3RB0LA3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB3LA0RB2RB---_2LA4LA1LA1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB4RB4RB---1RA_2LB3RA0LB4LA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB2LA3RB4RB0RB_0LB2LA1RA4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB3LA1RB4RB2RB_2LA---2LB1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB3RB3LA4LA1RB_0LB2LA2LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB3RB---0RA2LB_2LA4RB4RB4LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB3LA---4RB4LA_0LB2LA1LA0RA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB3RA3LB1RB---_2LA3RB4LA2RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB2RB4RB1LB1RB_1LA3RB1LA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB4RB0RB2LA3RB_0LB2LA3RA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB2RA3LA2RA2LB_2LA---4LB4RB0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB2RB3RB2RB3LB_1LA3LA---4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB2RB4RB1LA1RB_2LB2LA3RB1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB0RA3RB3RB2LB_2LA---3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB3LA1RB4RB0RB_2LA---2LB1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB4RA---4RB1LA_2LB3RB4LB1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB2LA3RB0RB2LA_0LB2LA1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB3LA1LB2RB---_2LA1RB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB2RA1LA2LB2LB_2LA3RB4LB0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB3RB---4LA1RB_2LA1LA2LB3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB3LA0LA3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB2RB2RA4LB---_2LA1LA3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB4RB---2LA0RB_2LB3RB1LA1LB4RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB2RB4RB4LB1RB_2LA---3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB4RB0LA0RB3LA_0LB2LA3LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB2RA3RB1LA---_2LA2RB4LA2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB4LA---0RB2LA_0LB2LA3RB1LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB2LA0RB---0RA_1LA3LA1RA4LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB3LB4RA2RA2LA_2LA---2RA4LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB3LA2LB0RB1RA_2LA---4LA4RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB3RA0LA4LA3RB_2LA---2LB1LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA0LA4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB0RA1LA1LB---_2LA3RB4LA0LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB4LA---0RB3RB_2LB3RB0LB4LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB2RA3RB2RB2LB_2LA0LA4RB---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB2RB4RB2LB1RB_2LA---3RB0LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB4RA2RB0LB1RB_2LB3LA3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB3LA3RA4RB0RB_2LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB2RA1LA2RB---_2LA3RB4LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB3RB---4LA0RB_2LA0LA1LB3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB4RB---1LA0RB_2LB2LA3RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB2RB4RA1LB1RB_1LA3RB1LA0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA2RB4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB2RB4RB1LB1RA_1LA3RB3LB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB3RA3LA4LA3RB_2LA0LA1LA---1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB2RB3LA1RB3LA_0LB1LA4LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB3LA0LA3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB3LA0LB2RB---_2LA1RA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB2RA3RB2RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB3LA---4RB0RB_1LB2LA1LA1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB3LA3LA0RB2RA_2LA0LB1LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB2RB3RB2RA3LB_1LA3LA---4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB3LA0LA1LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB3LA0LB0RB---_2LA1RA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB2RB4RB1LB1RB_1LA3RB1LA0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA3LA2LB0LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB3RB0RB2RB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1_T 4000%N. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB3LA1RB4RB2RB_2LA2LB1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB3RB---1RB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB3RA2LB4LA3RB_2LA---0LB3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB3LA---4RB0RB_1LB2LA1LA1RA4LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB3RB1LA2RB2LA_1LB2RA---4LA4LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB3RB1LA4RB1RB_2LA3LA3LB2RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB2RB4RB2LB1RB_2LA---3RB0LA3RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB3RB3LA4LA1RB_0LB2RB2LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB3RA3RB4RB1LA_0LB2RB3LA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA0LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB4RB3LA1RB3RB_1LB2RB0LA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB2RB4RB2LB1RB_2LA3RB1LB1LA---") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB2LA4RB2LA0RB_1LA1LB3RA---3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB2RB3LA4RB1RB_0LB1LA0LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA0LB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB2RB0RB---3LB_2LB1RA3LA4RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB2LA4LB1RB---_0LA4RB3LB2RA2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB2RB3RB0RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1RA3LB4RA---_2LA3LA2LB0RB3LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB3RA3RB4LA3RA_2LB1RA2LA0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB3RB3LA4RB1RB_2LA2RB1LB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB2LB1LA0RA---_2LA3RA3LB4RB3LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB2RB2RA4LB---_2LA2RB3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB2LA3RB4RB1RB_0LB2LA1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB3RB0LA4LA0RB_0LB2LA2LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB3RA1LA2RB---_2LA3RB4LA2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB2RB3LA0RB---_2LA4LA1LA2RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB3RB2RB0RB2LB_2LA---4RB2RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB3LA1RB4RB2RB_2LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB3RA1LA2RB---_2LB3RB4LB1LA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB2RA3RB1LA---_2LA2RB4LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB3LA1RB4RB0RB_2LA---0LB1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB3RB---4RB1LA_2LA4RA2LB3LA4LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB3RB0LA4LA0RB_0LB2RB2LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB3LA0LB0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB3LA0RB---2LB_2LA0RA3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA3RA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB3LA1LA4RA3LB_2LA3RA---1RA2LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB2LA4RB2LA0RB_1LA3LA3RA0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB4RB---1LA0RB_2LB2LA3RB1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB3RB---4LA1RB_2LA0LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB4RA3RB4RB1LA_2LB2RB3LA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB3RB---0RB1LB_2LA4RB1LA---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB3LA0LA3RB3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB3LA1RB0RB---_2LA1LA4LA1RA0LB") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB2LA3RB0RB2LA_1LA1LB1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA2RB4LA2RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB3LA0LA0RB3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB2LA3RB0RB1RB_0LB2LA1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB3LA3LB1RA---_2LA2LB3RA4RA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB3RB4LA1RB2LB_2LA---4RB2RA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB3RB2LA4LA0RB_2LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB2LA3RB0RB1RB_1LA4LA1RA---0LB") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB3RB3LA0RB---_2LA---4LB4LA2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB2RB4RB1LB1RB_2LA2LB3RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB2LA3RB0RB1RB_1LA0LB1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB3RB---1RA3LB_2LB3LA1LA4RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB3RB3LA4LA1RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB2RB0RA3RB3LB_1LA3LA---4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB3RB1LA2RB---_2LA2RA4LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB4LA---4LA0RB_1LB2LA3LA1LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB3RB---0RB2LB_2LA---3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB3LB4RB4LB1LB_2LA4RA1RA---2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB2RA3RB4RB1LA_0LB2RB3LA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB3RB3LB4RB1RB_2LA3LA1LA2RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB3RA4LB1RB---_2LA3RB3LA4LA2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB2LA4RB2LA0RB_0LB2LA3RA---3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB3RB2RB0RA1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB3LA---1RB1RA_2LB1LA0LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB3RB1LA2RB---_1LB2RA4LA2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB3RA1LA0RB2LB_2LA4RB4RB---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB2RB1RA2LB---_2LA2LA3RB4LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB3LA---4RB0RB_1LB2LA1LA1RA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB2LA0LA3RB3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB2LA3RB0RB1RB_0LB2LA1RA4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB3RB1LA2RB---_2LB2RA4LB2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB0RA3LB---1RB_2LA4RB4LA2RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB4LA0RB---1LA_0LB2RB3LA1LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB2RB4RB1LB0RB_1LA3RB0LA2LA---") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB0RA3LA2LB4RB_2LA---4LB4LA3RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB3LA1RB0RB---_2LB3LA4LB1RA0LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB1RA---2RB0LB_2LB1RB3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB3RB1LB4RB1RB_2LA2RB3LA1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB---2RB0RB0LB_2LB1RA3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB2RB0RB4LB---_2LA---3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB3LA2RB0RB1RA_2LA1LB1LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB3LA3LA0RB1RA_2LA0LB1LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB2RB4RB0LB1RB_2LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm177: ~halts (TM_from_str "1RB3RB0LA4LA0RB_2LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm178: ~halts (TM_from_str "1RB1RA3RB4RB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm179: ~halts (TM_from_str "1RB2RB0RA4LB---_2LA3RB3RB0LA1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm180: ~halts (TM_from_str "1RB3LA---4RB0RB_1LB2LA1LA1RA4RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm181: ~halts (TM_from_str "1RB2RB4RB0LB0RB_2LB3RB1LB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm182: ~halts (TM_from_str "1RB2LB1LB---1RB_1LA3RB4LB2RB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm183: ~halts (TM_from_str "1RB4RA2RB0LB1RB_2LB1RB3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm184: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA3RB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm185: ~halts (TM_from_str "1RB3LA4LA0RB3LA_2LA---2LB4RA2RA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm186: ~halts (TM_from_str "1RB3LA4LB4RB2RB_2LA---0LA4RA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm187: ~halts (TM_from_str "1RB2LA3RB0RB2LB_0LB2LA1RA4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm188: ~halts (TM_from_str "1RB2RA3RB1LA---_2LA2RB3LA4LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm189: ~halts (TM_from_str "1RB3LA4LB0RB---_2LA0LA1LA1RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm190: ~halts (TM_from_str "1RB2RB4RA1LB1RA_1LA3RB1LA0LA---") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm191: ~halts (TM_from_str "1RB1RA3RB4LB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm192: ~halts (TM_from_str "1RB4RA2RB0LB1RB_2LB2RB3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm193: ~halts (TM_from_str "1RB2RB3LA0RB3LA_2LA0RA2LB4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm194: ~halts (TM_from_str "1RB1RA1LB4RB---_2LA2RB3LA1LA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm195: ~halts (TM_from_str "1RB2RB4RA2LB---_2LA3RB1LB1LA1RB") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm196: ~halts (TM_from_str "1RB2LB4LB---1RA_2LA4LA3RA4RA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm197: ~halts (TM_from_str "1RB2LB4LA0RA---_2LA3RA3LB2RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm198: ~halts (TM_from_str "1RB3LA3LA4RB0RB_2LA---2LB2RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm199: ~halts (TM_from_str "1RB2RB4LA1LA0RB_2LA---3LA3LB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm200: ~halts (TM_from_str "1RB2RB4RB0LB1RB_2LB3LA3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm201: ~halts (TM_from_str "1RB1RA3RB0LA3RA_2LA4LA2LB4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm202: ~halts (TM_from_str "1RB1RA3LB---0RB_2LA4RB4LA2RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm203: ~halts (TM_from_str "1RB3LA---4LA0RB_0LB2LA1LA0RA4RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm204: ~halts (TM_from_str "1RB2LA0RB3LA---_1LA3LB1RA4LB1LB") c0.
Proof. solve_loop1_T 4000%N. Time Qed.

Lemma tm205: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA2RA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm206: ~halts (TM_from_str "1RB2RB4LA3LA0RB_2LB3LA---1LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm207: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA3LA2LB4RB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm208: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB3LA0LA0RB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm209: ~halts (TM_from_str "1RB3RB1RB2RB2LB_2LA---4RB4LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm210: ~halts (TM_from_str "1RB1RA3RB0RB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm211: ~halts (TM_from_str "1RB3RA2LA0RA2LB_2LA2RB4RB---0LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm212: ~halts (TM_from_str "1RB2RB0RA1LB---_1LA3RB3RB4LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm213: ~halts (TM_from_str "1RB3LA0LA0RB1RA_2LA---0LB4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm214: ~halts (TM_from_str "1RB0RA3RB2RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm215: ~halts (TM_from_str "1RB0RA3LB4LB2RA_2LA---4LA1LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm216: ~halts (TM_from_str "1RB2RB4LA0LA0RB_2LA---3LA3LB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm217: ~halts (TM_from_str "1RB3RB4LA4LA0RB_2LA---2LB3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm218: ~halts (TM_from_str "1RB3LB3LA2RA---_2LA4RA1LB1RA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm219: ~halts (TM_from_str "1RB3LA1RB0RB---_2LA3LA4LB1RA0LB") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm220: ~halts (TM_from_str "1RB2RB3LA1RB3LA_0LB1LA4LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm221: ~halts (TM_from_str "1RB3RB0LA4LA0RB_0LB2LA1RB---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm222: ~halts (TM_from_str "1RB1RA1LB4RB---_2LA2RB3LA1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm223: ~halts (TM_from_str "1RB4RB0RB0LB2RB_2LB3RB1LB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm224: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA2LB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm225: ~halts (TM_from_str "1RB3RB---4LA0RB_2LA0LB1LA3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm226: ~halts (TM_from_str "1RB3RB---4LA0RB_1LB2LA0LA3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm227: ~halts (TM_from_str "1RB3LA0LB4RB2RB_2LA---0LA4RA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm228: ~halts (TM_from_str "1RB1RA3RB0LB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm229: ~halts (TM_from_str "1RB2LB0LA0RA---_2LA3RA3LB4RB3LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm230: ~halts (TM_from_str "1RB2RB3LA0RB3LA_2LA3RB2LB4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm231: ~halts (TM_from_str "1RB3LA0RB2RB3LA_1LB2LA1LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm232: ~halts (TM_from_str "1RB2RB3LA0RB3LA_2LA2RA2LB4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm233: ~halts (TM_from_str "1RB3RB---4LA0RB_2LB1RB0LA3LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm234: ~halts (TM_from_str "1RB3LA0RA4RB0RB_2LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm235: ~halts (TM_from_str "1RB2LA0RB---2LA_2LB3LA1RA4LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm236: ~halts (TM_from_str "1RB3RB---1LA3RA_2LA4RA4LB3LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB2RB4RB1LA3RB_2LA3RA2LB---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm238: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA3LA4LA2RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm239: ~halts (TM_from_str "1RB2RB4RB1LB1RA_1LA3RB1LA0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm240: ~halts (TM_from_str "1RB2RA0RB3RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm241: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA1RB4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm242: ~halts (TM_from_str "1RB4RB---0LB1RB_2LB3RB1LB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm243: ~halts (TM_from_str "1RB2RB4RA1LB---_2LA2LB3RB0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm244: ~halts (TM_from_str "1RB1RA3RB---3LB_2LB3LA1LA4RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm245: ~halts (TM_from_str "1RB3RB---4LA0LB_2LA0LA1LA3RA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm246: ~halts (TM_from_str "1RB3RB0LA1RB0LB_2LA---4RB2RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm247: ~halts (TM_from_str "1RB2RA3RB0RB2LB_2LA---4RB2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm248: ~halts (TM_from_str "1RB3LA1RA2LB---_2LA3LB4RA2RA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm249: ~halts (TM_from_str "1RB3RB1RB2RB2LB_2LA---3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm250: ~halts (TM_from_str "1RB4RB1RB0LB2RB_2LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm251: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA1LA3LB0LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm252: ~halts (TM_from_str "1RB2RB4RB1LB1RB_1LA3RB3LB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm253: ~halts (TM_from_str "1RB4LA---4RB0RB_2LB0RB3LA0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm254: ~halts (TM_from_str "1RB3LA0RB2RB---_2LB1LA4LA1RA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm255: ~halts (TM_from_str "1RB3LA4RB2RB1RB_1LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm256: ~halts (TM_from_str "1RB3RB4LA2RB1RB_2LB2LA1LA---2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm257: ~halts (TM_from_str "1RB2RB3LA4RB1RB_0LB1LA4LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm258: ~halts (TM_from_str "1RB2RB0RA4LB---_2LA3RB3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm259: ~halts (TM_from_str "1RB4LA---4LA0RB_2LB1RB3LA0LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm260: ~halts (TM_from_str "1RB3LA1RB0RB---_2LA1LA4LB1RA0LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm261: ~halts (TM_from_str "1RB1RA---0RB0LB_2LB3RB4RB2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm262: ~halts (TM_from_str "1RB2RB1RA4LB---_2LA0RB3RB0LA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm263: ~halts (TM_from_str "1RB2RB4RB0LB1RA_2LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm264: ~halts (TM_from_str "1RB3RA2RB0RB1LB_2LA4RB1LA---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm265: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA2RB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm266: ~halts (TM_from_str "1RB2LA3RB0RB2LA_1LA4LA1RA---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm267: ~halts (TM_from_str "1RB1RA---2LB2RB_2LB2LA3RB4LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm268: ~halts (TM_from_str "1RB0LB4RA2LB2RA_2LA2RB3RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm269: ~halts (TM_from_str "1RB2LA3RB0RB2LA_0LB2LA1RA4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm270: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA1RB4LB1RA0LB") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm271: ~halts (TM_from_str "1RB3RA1LA0RB1LB_2LA4RB4RB---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm272: ~halts (TM_from_str "1RB2RB4LA4LA0RB_2LA3RA2LB---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm273: ~halts (TM_from_str "1RB4RB0LB1LA3RB_2LB3RA1LA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm274: ~halts (TM_from_str "1RB3RB---0RB3LB_2LA1RA4RB2LB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm275: ~halts (TM_from_str "1RB3RB---4LA0RB_2LA3LA2LB1LA3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm276: ~halts (TM_from_str "1RB2RA4RB2RB1LA_2LB3RB4LA---2LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm277: ~halts (TM_from_str "1RB1LB---4RB0RA_2LA4LB3RA1LB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm278: ~halts (TM_from_str "1RB2RB3LA0RB1LA_0LB1LA4LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm279: ~halts (TM_from_str "1RB2RA1LA4RB3LB_2LA3RB0LA2RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm280: ~halts (TM_from_str "1RB3LA4LA0RB3LA_2LA---2LB1RA2RA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm281: ~halts (TM_from_str "1RB2RB4LA3LA0RB_2LA---3LA3LB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm282: ~halts (TM_from_str "1RB2RA1LA2RB---_2LA3RB3LA4LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm283: ~halts (TM_from_str "1RB3LB3RA4LB1LB_2LA2LB3RB1RA---") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm284: ~halts (TM_from_str "1RB2LA1RB1RA---_1LA4LA3RA1LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm285: ~halts (TM_from_str "1RB2RA3RB4RB1LA_2LB2RB3LA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm286: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA0LA4LA2RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm287: ~halts (TM_from_str "1RB2RA3LA2RB---_2LA4LA1LA1RA2LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm288: ~halts (TM_from_str "1RB3RB1LB4RB1RB_2LA2RB4LA---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm289: ~halts (TM_from_str "1RB2RB4LA0LA0RB_1LA3LA---1LB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm290: ~halts (TM_from_str "1RB3RA2RB0RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm291: ~halts (TM_from_str "1RB2RB4LA---0RB_1LA3LB2LA0LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm292: ~halts (TM_from_str "1RB3RB1RB2RB2LB_2LA---4RB4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm293: ~halts (TM_from_str "1RB3LA1RB2RB---_2LA---4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm294: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA4LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm295: ~halts (TM_from_str "1RB3RB1LA2RB2LA_2LB2RA0LB4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm296: ~halts (TM_from_str "1RB3RB0LA4LA0RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm297: ~halts (TM_from_str "1RB2RB4RB1LB1RB_1LA2LB3RB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm298: ~halts (TM_from_str "1RB3RA2LB4LA1RA_2LB1LA---3LA3RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm299: ~halts (TM_from_str "1RB3LA1RB0RB---_2LA---4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm300: ~halts (TM_from_str "1RB2RB3LA0RB---_2LB1LA4LA2RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm301: ~halts (TM_from_str "1RB4RB0LB1LA3RB_2LB3RA---1LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm302: ~halts (TM_from_str "1RB3RA3LB4LA3RA_2LA0RB1RA0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm303: ~halts (TM_from_str "1RB3LA1RB4RB0RB_2LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm304: ~halts (TM_from_str "1RB3LA3LB0RB---_2LA0LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm305: ~halts (TM_from_str "1RB2RB0RA3RB3LB_2LA---3LA4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm306: ~halts (TM_from_str "1RB3LA0LA0RB1RA_2LA---4LB4RA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm307: ~halts (TM_from_str "1RB3LA0LB1RA0RB_2LB2LA1RB4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm308: ~halts (TM_from_str "1RB3RB---1RB2LB_2LA---4RB0LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm309: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA3LA4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm310: ~halts (TM_from_str "1RB3RB3LA4RB1RB_2LA---4LB4LA2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm311: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA0RA4LA2RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm312: ~halts (TM_from_str "1RB2RB3RB1LB---_2LA4RA3LB0LA1LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm313: ~halts (TM_from_str "1RB3RB---4RB1LA_2LA4RA3LA0LB3RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm314: ~halts (TM_from_str "1RB2RB4RB1LA1RB_2LB2LA3RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm315: ~halts (TM_from_str "1RB3LA3LA0RB---_2LA0RA4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm316: ~halts (TM_from_str "1RB3RB1RB2RB3LB_2LA---4RB4RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm317: ~halts (TM_from_str "1RB0RA4RB2LB2LA_1LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm318: ~halts (TM_from_str "1RB2LA0RB4LA2LA_1LA3LA1RA1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm319: ~halts (TM_from_str "1RB3RB1LA2RB2LA_2LB2RA2LB4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm320: ~halts (TM_from_str "1RB3RB1RA4LA0RB_2LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm321: ~halts (TM_from_str "1RB2LA3RA4LB1LA_1LA0RB1RA2LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm322: ~halts (TM_from_str "1RB3RB---4LA0RB_2LA2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm323: ~halts (TM_from_str "1RB2RA3LA2RB0LA_2LB2RA4LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm324: ~halts (TM_from_str "1RB3LA0RB4RB0RB_2LB2LA1LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm325: ~halts (TM_from_str "1RB3LA2LB1RB1RA_2LA---4LA4RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm326: ~halts (TM_from_str "1RB3LA---4RB0RB_1LB2LA1LA1RA1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm327: ~halts (TM_from_str "1RB3RA2LA0RB1LB_2LA4RB4RB---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm328: ~halts (TM_from_str "1RB2RB1RA2LB---_2LB2LA3RB4LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm329: ~halts (TM_from_str "1RB2RB4RB2LB0RB_2LA---3RB4LA0LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm330: ~halts (TM_from_str "1RB2RB4LA2LA0RB_1LA3LA---1LB2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm331: ~halts (TM_from_str "1RB3RB1RA4LA0RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm332: ~halts (TM_from_str "1RB3LA1LB0RB---_2LA3LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm333: ~halts (TM_from_str "1RB4RB1RB1LA2RB_2LB2LA3RB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm334: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA3LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm335: ~halts (TM_from_str "1RB3RA0LB4LA3RB_2LA---0LB3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm336: ~halts (TM_from_str "1RB3LA0RB2RB---_2LA4LA1LB1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm337: ~halts (TM_from_str "1RB3LB1LA2RA---_2LA4RA1LB1RA3RA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm338: ~halts (TM_from_str "1RB2RB0RA1LB---_1LA3RB1LA4LA0LA") c0.
Proof. solve_loop1_T 2000%N. Time Qed.

Lemma tm339: ~halts (TM_from_str "1RB2LA3RB4RB1RB_0LB2LA1RA4LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm340: ~halts (TM_from_str "1RB3LA4LA0RB2LB_2LB2LA3LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm341: ~halts (TM_from_str "1RB3LA---1RB1RA_2LB1LA4LA4RA2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm342: ~halts (TM_from_str "1RB3RB2LA4LA0RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm343: ~halts (TM_from_str "1RB3RA2LA0RB2LB_2LA4RB4RB---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm344: ~halts (TM_from_str "1RB3RB3LA4LA1RB_0LB2LA1RB---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm345: ~halts (TM_from_str "1RB3RB3LA4RB1LA_2LA4RA0LB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm346: ~halts (TM_from_str "1RB2LB0LA0RA---_2LA4RA3LB2RB2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm347: ~halts (TM_from_str "1RB2RB0RA2LB---_1LA3RB3RB4LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm348: ~halts (TM_from_str "1RB2LA3RB4RB0RB_0LB2LA1RA4LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm349: ~halts (TM_from_str "1RB3RB1LA2RB---_1LB2RA4LB2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm350: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB2LA0LA3LA1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm351: ~halts (TM_from_str "1RB3RB---0RB3LB_2LA1RA4RB2LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm352: ~halts (TM_from_str "1RB4RB---0LB0RB_2LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm353: ~halts (TM_from_str "1RB3RA3LB1LA1RB_2LA4RB1RA0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm354: ~halts (TM_from_str "1RB3RB---4LA0RB_1LB2LA0LA1RB3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm355: ~halts (TM_from_str "1RB3RB4RA4LA0RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm356: ~halts (TM_from_str "1RB4RB1RB1LA2RB_2LB2LA3RB1LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm357: ~halts (TM_from_str "1RB3RB---0RA1LB_2LA4RB4RB4LB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm358: ~halts (TM_from_str "1RB2RB4RA1LB1RB_1LA3RB3LB0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm359: ~halts (TM_from_str "1RB3RB3LA4RB1LA_2LA4RA3LB2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm360: ~halts (TM_from_str "1RB3LA4LB0RB2LA_2LB2LA3LA1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm361: ~halts (TM_from_str "1RB2RB3LA4RB1RB_2LB2LA1LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm362: ~halts (TM_from_str "1RB2RB4RA1LB1RB_1LA3RB0LA0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm363: ~halts (TM_from_str "1RB3LA2LB0RB---_2LA1LA4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm364: ~halts (TM_from_str "1RB4RA---4RB3LA_2LB3RB0LA1RA4LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm365: ~halts (TM_from_str "1RB2RB3LA0RB1RB_0LB1LA4LA2RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm366: ~halts (TM_from_str "1RB2RB3LA0RB3LA_2LB2LA1LA4RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm367: ~halts (TM_from_str "1RB4RB1LB1LA0RB_2LB2LA3RB0RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm368: ~halts (TM_from_str "1RB2LA0RB2LA3LA_1LA4LA3RA---1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm369: ~halts (TM_from_str "1RB3LA0LA4RB0RB_0LB2LA3RB1RA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm370: ~halts (TM_from_str "1RB3LA1LB0RB---_2LA1RB4LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm371: ~halts (TM_from_str "1RB2RB4LA---0RB_2LA3LA2LB4LA2RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm372: ~halts (TM_from_str "1RB3LA3LA4RB0RB_2LA---2LB1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm373: ~halts (TM_from_str "1RB3LA3RB0RB---_2LA3LA4LA1RA0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm374: ~halts (TM_from_str "1RB2RA1LA2RB---_2LA3RB4LA2LA3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm375: ~halts (TM_from_str "1RB3RA3LB4LA3RA_2LA2RB1RA0LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm376: ~halts (TM_from_str "1RB2RB4RB1LB2RB_1LA3RB0LA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm377: ~halts (TM_from_str "1RB2RB4RB2LB1RB_1LB2LA3RB1LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm378: ~halts (TM_from_str "1RB0RA3RB0LA2LB_2LA---3LB4RB3LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm379: ~halts (TM_from_str "1RB3RB1RB4LA0RB_0LB2LA1LA---3RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm380: ~halts (TM_from_str "1RB3LA1RB4RB2RB_2LA---0LB1RA0LA") c0.
Proof. solve_loop1. Time Qed.

