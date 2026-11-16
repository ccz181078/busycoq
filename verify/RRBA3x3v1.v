From BusyCoq Require Import Individual33.
From BusyCoq Require Import RRBA.
From BusyCoq Require Import TMAddOneSymbol.
Module BB33' := TMAddOneSymbolCtx BB33.
Module RRBA33 := RRBA BB33'.
Module BB33'spec := TMAddOneSymbol BB33.
Require Import NArith.
Require Import String.


Ltac solve_loop1'' min_b n_skip k T :=
  rewrite halts_halts';
  apply BB33'spec.from_nonhalt;
  rewrite <-RRBA33.TM.halts_halts';
  apply (RRBA33.decide_loop1_spec' _ (min_b,8%nat) n_skip k T).
Ltac solve_loop1' n_skip k T := solve_loop1'' 8 n_skip k T.
Ltac solve_loop1_T T := solve_loop1' 1%nat O T; native_cast_no_check (eq_refl true).
Ltac solve_loop1 := solve_loop1_T 600%N.


Lemma tm1: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_2RB0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RB1LC_1LA2RB0LA_2RB---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RB0LC_1LC2LC2RB_---1RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB2LA1RA_1LC2RC---_1RA0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LC---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0RB2LC_2LA0LA2RB_0LA---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1RA0LA_2RC2RB1LB_2LC---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB2RB1LC_2LC2RB1LB_---1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_2RA0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_1LC---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB2LB0LC_2LA2RB1LB_---1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB2LA0RC_1LA---1RA_1LB0LB1RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0RC0LC_2LC2RB1LC_---2RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_2LB---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB---0LC_2RC2RB1LB_2LA1RA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0LB---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB2RA1LA_2LA0RC---_2LA2RB2LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB2LC---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB0RB1LC_2LA2RB1LA_---2RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB2RB---_2RC2RA1LB_2LC1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB1LB0LC_2LA2RB1LB_---1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RB1LC_2LA2RB1LA_---1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0RB0LC_1LB2RB1LA_1RB---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB---1RC_2LB1RA0LB_0RB2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB2LA1RA_1LB0LC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0RB2LC_1LC2RB0LC_---1LA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB2LC---_2LB0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0RB---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB1LA0RB_2LA1RC0LA_---2RB1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB1LA0RB_2LA1RC0LA_---2RB2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB1LA0RB_2LA1RC0LA_---2LB2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_0RB---0LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB2LA0RB_1LA0LA1RC_---1RB2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB2LC---_1LC1RB0LC_2RC1LA0RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB2RB1LA_2LA2RC2LB_---0RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB2RA1LA_2LA0RC2LC_---2RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB2RB1LA_2LA2RC0LA_0LA0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB2RB2LA_2RC---2RC_1LA0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0RC---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB2LA1RA_1LC0LC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB2LA1RA_1LC2RC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB2LC---_2LA0RB0LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB0RB2LC_2LA0RA2RB_0LA---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB------_2RC2RB1LB_2LC1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1RB---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB2LC---_2LC0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB2LA0RB_2LA---1RC_1LA0LA2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB2LC---_1LC2LA1RB_2RC1LA0RB") c0.
Proof. solve_loop1_T 1000%N. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0RB0LC_2LC2RB1LC_---2RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB1RA0LA_2RC2RB1LB_2LA------") c0.
Proof. solve_loop1. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB2LA1RA_1LC1LC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB2RC---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB2RB2LA_1LC2LA2RB_---1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB2RA1LA_2LA0RC---_---2RB2LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB1RA0LA_2RC2RC1LB_2LA2RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1RB0LA_2LA---1RC_2RB2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB0LC---_0LB2LA1RA_2RA1LC0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB0RB0LC_1LC2LC2RB_---2RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB---0LC_0RC2RB1LB_2LC1RA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB0RB1LC_2LC0LC2RB_---2LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB2LA1RA_1LC1RA---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RB2LC_1LA2LA2RB_---1LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB---2RB_2LC2RB1LB_---1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB2RB1LA_0LA2RC---_2LA0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB2LA1RA_1LC1RC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB2RA1LA_2LC2RB2LA_---0RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_0RA0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB1LA0RB_1LA1RC---_2LA2RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB2RB1LA_2LA2RC0LA_2RB0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB0RB2LC_2LA0LA2RB_2RB---1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_0RB---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB2LA1RA_1LC2LA---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB0RA2LC_1LC2RB1LB_1RA2LB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB0RB1LC_2LA2RB1LA_---2LA0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB0LC---_2LB2LA1RB_2RA1LA0RA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB1RA0LA_2RC2RB1LB_2LC---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB2RB0LC_2LA2RB1LB_---1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB2RB2LA_0LA---2RC_1LA0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB1RA0LA_1RC2RB1LB_2LC0LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_1RA0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB2LA---_2RC0LC1RC_1LC2LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB0RB0LC_2LC2RB1LC_---1RB1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB1LB---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB0RB2LC_1LA2LA2RB_---0RC0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB2RB1LA_2LA2RC0LA_0RB0RB---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB---2RC_2LB1RA0LB_2RB2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB2LA1RA_1LC0LA---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB1RA0LC_2RC2RB1LB_2LC---0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB1RB1LA_2LC2RB1LB_---1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB2LA---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_0RB0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB2RB2LB_2LC0RA---_1RB2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB2RB2LA_0LC---2RC_1LA2LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB2RB1LA_0LA1RC0RB_0LC2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_2RC0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0RB0LB_1LC2RB1LA_---1LA2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB2LC---_1RC0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB1RB0LC_2LA2RB1LB_---1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_2RB0LC0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB1LA0RB_2LA1RC0LA_---2RB1LB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB---0LC_2RC2RB1LB_2LA1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB2RA0LC_2LA2RB1LB_---1RA1LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB2LA1RA_1LC0RC---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB2RB0LA_1LC2LA2RB_---1RA0LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB2LA1RA_1LC2RB---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB2RB2LA_0LA---2RC_1LA0LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB2LA0RB_1LA0LA1RC_---2RB2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB2LB---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB0RB2LC_1LA2LA2RB_---1RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB0LC2RA_1LA2LB1RB_2RA2LA---") c0.
Proof. solve_loop1. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB2LA1RA_1LC2RA---_1LA0LC2RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB0RB1LC_1LA2RB0LA_0LA---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_0LA---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB2LC---_1LC1RB0LC_2RB1LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB2LC---_0LA0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB---2RB_1LC0LC0RA_1RC2LC1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB2LC---_2LA0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB0RB0LA_2LA---1RC_2RB2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB2RB1LA_2RC2RC---_2LA0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB---2LC_1LB2RB1LC_1RB0RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB0RB0LC_1LB2RB1LA_1LA---2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB0RB0LB_1LC2RB1LA_---1RB2LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB2LC---_1LA0RB2LA_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB1RC0LA_2RC2RB1LB_2LA---1RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB1LC---_2LC0LC1RB_2RB2LA0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB0RB2LC_1LA2LA2RB_---2RB0LA") c0.
Proof. solve_loop1. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB2RB2LA_1LA0LA2RC_2RB---0RB") c0.
Proof. solve_loop1. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB0LA---_2LC0RB2LB_1LA2RC1LC") c0.
Proof. solve_loop1. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB2LA1RA_1LC0RB---_2RA0LC2RC") c0.
Proof. solve_loop1. Time Qed.

