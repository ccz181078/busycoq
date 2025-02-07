From BusyCoq Require Import Individual62.
From BusyCoq Require Import RRBA.
Module RRBA62 := RRBA BB62.
Export RRBA62.
Require Import NArith.
Require Import String.


Ltac solve_loop2'' min_b n_skip k T :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    apply (decide_loop2_spec' _ min_b n_skip k T);
    native_cast_no_check (eq_refl true)
  end.
Ltac solve_loop2' n_skip k T := solve_loop2'' (O,O) n_skip k T.
Ltac solve_loop2 k T := solve_loop2' O k T.

Close Scope sym.

(* previously solved by fold tape CTL, but now we use RRBA(loop2) to solve them *)

Lemma tm1: ~halts (TM_from_str "1RB---_0LC1RF_1RE1LD_1LC0LD_---0RB_1RB0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0LC_0LF1RE_1RD0RE_---1LC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB0RA_0LC1RA_---0RD_0LE0RB_1RD1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB1LD_1RC0RF_0LA0RC_1RE0LD_1LA0RB_---1LB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LD_1RC1LB_0LA0RC_1RE0LD_1LA0RF_---0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0RA_0LC1RA_---1LD_1LE0LD_1RF1LF_1LE0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB0RA_0LC0RB_1RE1LD_1LC0LD_1RB0RF_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0RE_0LC1RF_1RA1LD_1LC0LD_---1RF_1RB0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB1LF_0LC1RE_---0RD_1LA0RB_0LA0RE_1RD0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0RA_0LC1RA_---1LD_1LE0LD_1RF1LD_---0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB1LD_1RC1RF_0LA0RC_1RE0LD_1LA0RB_---0RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RF_0RB1LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB0RA_0LC1RA_0LE1LD_1LC0LD_0RF0RB_1RE---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_1RF0LB_0RB---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB1LE_1LC1RD_---1RB_0LA0RD_1RF0LE_1LA0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RF_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0RA_0LC1RE_1RE1LD_1LC0LD_1RB0RF_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB1LD_1RC1LD_0LA0RC_1RE0LD_1LB0RF_---1RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB1LE_1LB1RC_---1RD_0LA0RD_1RF0LE_1LA0RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB1RC_1RC---_0LD0RC_1RB1LE_1RF0LE_1LD0RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB0RF_0LC1RA_1RA1LD_1RE0LD_1LC0RB_---0RA") c0.
Proof. solve_loop2' 1 5 1000%N. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_1RF0LE_0RB---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0RB_0LC1RF_---1LD_1LE0LD_1RA1LD_1RB0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0RA_0LC1RA_---1RD_0LE0RB_1RD1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB0RA_0LC0RB_1RE1LD_1LC0LD_0LF0RF_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0LC_---1RE_1RF0RE_0LA1RE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0RA_0LC1RA_0LE1LD_1LC0LD_0RF---_1RF0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_---1RF_0RB1LD") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB1LD_1RC0RB_0LA0RC_1RE0LD_1LA1RF_---0LB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB0RA_0LC1RA_---1LD_1LE0LD_1RF1LF_0RC0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB0RA_0LC1RE_1RE1LD_1LC0LD_0LF0RF_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_1RF1LB_---0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0LF_0RB1RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0RE_0LC---_1RA1LD_1LC0LD_0LC1RF_1RE0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB0RA_0LC1RA_1RE1LD_1LC0LD_0RB0RF_---1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB1LD_0LC0RE_---1LD_1LA0LD_0LC1RF_1RE0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1RE0LD_1LA0RF_---1RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB1LE_0RC0RD_0LD---_0LA1RF_1LA0LE_1RD0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_1RF1LE_---0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1RE0LD_1LA0RF_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB0RA_0LC1RA_0RE1LD_1LC0LD_---1LF_1RF0RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB0RD_1LC0LD_0LF1RA_0RE0RF_1LB---_1RA0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB0RF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0RB0RE_0RB1RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB0RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA---_0RF1RD_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LB0RE_0RB1RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LE0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LB0RE_0RB0RF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB1RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB0LA_0RC1LA_0LD1RE_0LE---_0RF0RD_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD0LC_0LE0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB1RF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1LD0RF_0RC1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LE0RE_0RB1RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB0RC_1RC1LE_0RD---_1LA1RF_0LB1RF_0RA0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB1LA_0RC1LE_1LD1RF_1LE---_0LA0RB_0RE0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0RB0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LC0RE_0RB1RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LB0RE_0RB1RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RE_0LC0RD_1RB1LC_1RA1LB_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD1RF_1LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0RB0RE_0RB1RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB0LA_0RC0LE_0LD1RE_1LA---_0RF1RD_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB0LA_0RC1LA_0LD1RE_1LA0RB_0RD0RF_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LB0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LA0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1RB0RE_0RB1RF_1LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_1LC0RE_0RB0RF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0LE0RE_0RB0RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0LE_0LC0LF_1LA0RD_1RC1RB_1LB---_0LA1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE0RD_0RF0LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RC_1RC0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_0RF0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RC0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB---_0RC0LC_0LD0LA_0RE0LF_1LD1RE_1LB1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE0RD_1RB0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB0LC_1LA1RD_0LD1LF_0RE0LB_1LD1RE_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB---_1LC0RF_0RE0LD_1LE0RD_1RB0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC1LF_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB---_0RC0LE_1RD0LF_1LB0RF_1LC0RE_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB---_0RC0LE_1RD0LF_1LB0RF_1LC1RB_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RC_0RF0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0RD_0LC0LF_0RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB0LC_1LA1RD_0LD1LF_0RE0LB_1LD1RE_1RE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC1LF_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC1LF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_0LC0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB0LE_0RC0LD_1LB1RC_1LA1RB_0LB1LF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC1LF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB---_1LB0LC_1LD1RD_0RE0LE_0LF1LA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB---_1RC0LF_1LD1RC_0RC0LE_1LB1RD_0LD0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RC_0LC0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB0LC_1LA1RD_0LD1LF_0RE0LB_1LD1RE_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RE_0RF0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_1RC0LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB0LE_1LC1RB_0RB0LD_1LA1RC_0LC0LF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0RD_0LC1LF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE0RD_0RF0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_0LB0LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB---_1LC0LD_0RA0LD_1LE1RE_0RF0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1RC_1RB0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB0LC_1LA1RD_0LD0LF_0RE0LB_1LD1RE_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1RC_0LC0LF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LF_---0LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB---_1LC0RB_0LF1LD_1RD1LE_0RA0LE_1RA1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LE_---0LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LF_0RA0LE_---1RA") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LE_0RF0LE_1RB---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB0LD_0LC---_1LD0LC_0RE1LC_1LA1RF_1RE0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB0LF_1LC1RE_1LD1RD_0RB0LD_1LA0RE_---1LD") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB---_1LC0RB_1RC1LD_1RE0LE_1RA1LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF1RE_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB---_1LC0RB_1RC1LD_0LE0LF_0RA0LE_1RA1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB---_1LC0RB_0LF1LD_0LE---_0RA0LE_1RA1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LF_---1RD_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB---_1LC0RB_0LF1RD_0LE1LD_0RA0LE_1RA1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB---_1LC0RB_0LE1LD_1RE---_1RA1LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LF_0RA0LE_---0LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB---_1LC0RB_0LE1RD_1RE1LD_1RA1LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LD_1RA1LF_0RA0LE_---0RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB1LE_1LC0RD_1RE0LD_0RE1RF_0LB0RA_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB1LC_1LC0RF_0LD0RA_1LE---_1RC0LF_0RC1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB1LA_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB1LA_0RC1LD_1RD1RE_0LA0RB_0RD1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB1LA_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0RF_1RC1LB_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB0LC_1LA0LD_1LA0LB_0RA1RE_0RF---_1RD0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB0LF_1RC0LE_1RD0RC_1LB0RD_0LA1LB_---0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD1RE_0LA0RB_0RD0RF_1LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB1LE_1LC0RD_1RE0LD_0RE1RF_0LF0RA_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB0LA_0LB1RC_0RD0RE_1LE1RF_1LA0RD_---0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB0LA_0LC0RC_0RF1RD_1LE---_1RF0LC_0LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB1LA_0RC1LD_1RD1RE_0LA0RB_0RD0RF_1LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB0LA_0RC1RF_1LD1RE_1LA0RC_---0RF_0RC0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB1LD_0RC0RF_1LD1RE_0LA0RB_0RD0LE_0LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB1LA_0RC1LD_1LA1RE_0LA0RB_0RD1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD1RE_0LA0RB_0RD0RF_0LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB0LA_1LC0RD_1RE0LD_0RE1RF_0LB0RA_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB1LC_0LA0RE_0LD0RA_1RC1LD_0RC1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB1LA_0RC1LD_1LA1RE_0LA0RB_0RD0RF_1LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD1RE_0LA0RB_0RD0RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB1LA_0RC1LD_1RD1RE_0LA0RB_0RD0RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB1LA_0RC1LD_1LA1RE_0LA0RB_0RD0RF_0LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0RE_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB1LA_0RC1LD_1RD1RE_0LA0RB_0RD0RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB1LF_0LC0RC_0RF1RD_1LE---_1RF0LC_0LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB0LB_1LA1LC_0RA1RD_1RE0RD_0LE0RF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD1RE_0LA0RB_0RD1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD1RE_0LA0RB_0RD0LE_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB1LA_0LA0RC_1RD1LB_0RE0RF_1RA---_0RB1RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB0LA_1LC0RD_1RE0LD_0RE0RF_0LB0RA_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB1LE_1LC0RD_1RE0LD_0RE0RF_0LB0RA_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB1LB_0LC0RC_0RF1RD_1LE---_1RF0LC_0LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD0RA_1RC1LD_0RC1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB1LD_0RC0RF_1LD1RE_0LA0RB_0RD0LB_0LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA0RD_0RB0RF_1RC0LE_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB1LC_0RC0RF_0LD0RA_1LE---_1RC0LF_0RC1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB1LE_1LC0RD_1RE0LD_0RE1RF_0LB0RA_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB0LA_1LC0RD_1RE0LD_0RE0RF_0LB0RA_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB0LA_1LC0RD_1RE0LD_0RE1RF_0LF0RA_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD1RE_0LA0RB_0RD0RF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB1LD_0RC1RF_1LD1RE_0LA0RB_0RD0LE_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm168: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm169: ~halts (TM_from_str "1RB0RA_1LB1RC_1RA1LD_1LF0LE_1LC0LD_---1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm170: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF0RE_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm171: ~halts (TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD0LF_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm172: ~halts (TM_from_str "1RB---_1LC1RB_0LE1RD_0RB0LC_1LD1LF_0LD0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm173: ~halts (TM_from_str "1RB1LA_1LC0RF_0RA0LD_1LE---_1LB0LF_0LC0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm174: ~halts (TM_from_str "1RB0RF_1LC0RA_1RE0LD_1LE---_0LB0LF_0LC1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm175: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF1RD_0RA1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm176: ~halts (TM_from_str "1RB1LB_0RC---_0RD1LE_0RE0RF_1LF0LF_0LA0LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm177: ~halts (TM_from_str "1RB---_1LC1RB_0RB0LD_1LE1RC_1RD0LF_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm178: ~halts (TM_from_str "1RB1LA_1LC0RF_0RA0LD_1LE---_0LB0LF_0LC0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm179: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_0RA1LF_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm180: ~halts (TM_from_str "1RB0RA_1LC0RA_1RA0LD_1LE1LE_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm181: ~halts (TM_from_str "1RB---_1LC0RB_0LE0RD_0LF1LA_0RF1LD_1RB0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm182: ~halts (TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD1LF_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm183: ~halts (TM_from_str "1RB---_1LC1RB_0LE1RD_0RB0LC_1RD1LF_0LD0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm184: ~halts (TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD0LF_1LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm185: ~halts (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm186: ~halts (TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA0LF_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm187: ~halts (TM_from_str "1RB1LA_1LC0RF_0RA0LD_1LE---_0LB0LF_0LC1RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm188: ~halts (TM_from_str "1RB1LE_1LC1RB_0LA1RD_0RB0LC_0LD0LF_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm189: ~halts (TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RF1LE_0LA0LF_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm190: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RB1LF_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm191: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF0RA_0RA1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm192: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF0RE_0RA1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm193: ~halts (TM_from_str "1RB1LA_1LC0RF_0RA0LD_1LE---_0LB0LF_0LC0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm194: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_0RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm195: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1LB1LF_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm196: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RC1LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm197: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RC_0LA1RB_0LB0LF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm198: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF1RD_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm199: ~halts (TM_from_str "1RB0LC_1LC0RB_0LD1RB_0RA1LE_0LA1LF_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm200: ~halts (TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LE1LE_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm201: ~halts (TM_from_str "1RB0RC_1LA0RF_0LB1LD_0LE---_1LC0LE_1RB0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm202: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_0LB0LE_0LF0RA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm203: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RA1LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm204: ~halts (TM_from_str "1RB0RA_1LC0RA_1RE0LD_1LE---_0LB0LF_0LC1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm205: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RB1LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm206: ~halts (TM_from_str "1RB---_0RC0RA_0LD1RF_1LE1LF_1RC0LE_0LB1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm207: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1LB1LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm208: ~halts (TM_from_str "1RB---_0RC0LF_1LB1RD_0RE0LC_1LD1RE_0LD0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm209: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_1RA1LF_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm210: ~halts (TM_from_str "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm211: ~halts (TM_from_str "1RB---_0RC0LD_1LD1RC_0LE1RB_0RA1LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm212: ~halts (TM_from_str "1RB0RF_1LC1RE_1LD0LC_1RB0LE_1LB0LA_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm213: ~halts (TM_from_str "1RB1LF_1RC0RD_1LB---_0LA1RE_1RD0RE_1LA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm214: ~halts (TM_from_str "1RB1LE_1LC0RF_1RD0RC_0LA1RC_1LA0LE_---1RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm215: ~halts (TM_from_str "1RB0RE_0LC0RB_1RA1LD_1LC0LF_---1RC_0RA0LF") c0.
Proof. solve_loop2' 1 5 2000%N. Time Qed.

Lemma tm216: ~halts (TM_from_str "1RB1LF_0LC0RD_1RD0RC_0LE1RC_---1LF_1LA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm217: ~halts (TM_from_str "1RB0RD_0LC---_1RD0RC_0LE1RC_1RA1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm218: ~halts (TM_from_str "1RB1LE_0LC0RF_1RD0RC_0LA1RC_1LA0LE_---1RC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm219: ~halts (TM_from_str "1RB0RD_1LC---_1RD0RC_0LE1RC_1RA1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm220: ~halts (TM_from_str "1RB---_0LC0RB_1RA1LD_1RE0LD_1LC0RF_1RC1RB") c0.
Proof. solve_loop2' 1 5 1000%N. Time Qed.

Lemma tm221: ~halts (TM_from_str "1RB1LF_0RC0RE_1RD---_1RE0RD_0LA1RD_1LA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm222: ~halts (TM_from_str "1RB1LF_1LC0RD_1RD0RC_0LE1RC_---1LF_1LA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm223: ~halts (TM_from_str "1RB1LA_1LC1RD_---1LD_0RE0LF_1RF1RA_1RB0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm224: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA1RE_0RC0LD_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm225: ~halts (TM_from_str "1RB0LB_1LC1RD_---1LD_1RE0LA_1LE0RF_1LB1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm226: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA1RB_0RC0LD_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm227: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA1RF_0RC0LD_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm228: ~halts (TM_from_str "1RB1LD_0RC0LE_1LD1RA_0LA0RB_0LD0RF_1RE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm229: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RA_0LA0RD_0RC0LD_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm230: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD1RA_0LA1RE_0RC0LF_---0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm231: ~halts (TM_from_str "1RB0LB_1LC1RD_---1LD_1RE0LA_1LE0RF_0LE1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm232: ~halts (TM_from_str "1RB0LE_0LC---_1LA1RD_1RC0RD_0RC1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm233: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RF_0RA1LE_1LD0LE_1RC---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm234: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RB_---1LE_1LF0LE_0RC1LE") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm235: ~halts (TM_from_str "1RB---_1RC0RB_1LD1RB_---0LE_0RC1LF_1LE0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm236: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA0RF_0RA1LE_1LD0LE_0LA---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm237: ~halts (TM_from_str "1RB0LF_1LC1RE_1LD1LD_0RB0LD_1LA0RE_---1LD") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm238: ~halts (TM_from_str "1RB0LC_1LC1RF_---1LD_0RE0LD_0LA1RF_1LA0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm239: ~halts (TM_from_str "1RB0LA_1LC1RE_---1LD_0RB0LA_1LF0RE_1RB0LC") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm240: ~halts (TM_from_str "1RB0LD_1RC---_1LA1RF_0RC1LE_1LD0LE_1RC0RF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm241: ~halts (TM_from_str "1RB0LE_1LC1RD_1LF1RD_1LA0RD_---1LF_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm242: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RB_0RF1LE_1LD0LE_---1RB") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm243: ~halts (TM_from_str "1RB0LF_1LC1RE_1LD0RD_0RB0LD_1LA0RE_---1LD") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm244: ~halts (TM_from_str "1RB0RA_1LC1RE_1LF0LD_1LE0LC_1RA1LC_---1LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm245: ~halts (TM_from_str "1RB0RA_1LC0RB_0LE0LD_1RA1LF_0LC0LF_---1LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm246: ~halts (TM_from_str "1RB0RA_1LC1RA_---0LD_1RA1LE_1RF0LE_1LD0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm247: ~halts (TM_from_str "1RB1RF_0LC---_1RA1LD_0LE1LC_1LC0LB_0RA0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm248: ~halts (TM_from_str "1RB0LD_0LC0RD_1LA1LC_1RB0RE_0RB1RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm249: ~halts (TM_from_str "1RB0LD_0LC0RD_1LA1LC_0LF0RE_0RB---_0RA0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm250: ~halts (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE1LA_1RA0LF_0LC1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm251: ~halts (TM_from_str "1RB0LF_1RC1RB_1LD0RB_---0LE_1LA1LB_0LD1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm252: ~halts (TM_from_str "1RB1RE_0LC0RD_1RD1LC_0RA1LB_0RB0RF_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm253: ~halts (TM_from_str "1RB1LB_1LC0RD_1LA0LC_1RE0RD_---0RF_1RB0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm254: ~halts (TM_from_str "1RB0LB_1LC0RE_1LD0LC_1RE1LB_1RF0RE_---0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm255: ~halts (TM_from_str "1RB0LD_0LC0RD_1LA1LC_0LF0RE_0RB---_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm256: ~halts (TM_from_str "1RB---_1RC0RF_0RD1LE_1LE0RB_1LB0LF_0LA0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm257: ~halts (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE1LA_1RF0LF_0LC1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm258: ~halts (TM_from_str "1RB1RA_1LC0RA_---0LD_1LE1LA_1RD0LF_0LC1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm259: ~halts (TM_from_str "1RB---_1RC1LB_0RD1LE_1LB1RF_0LB0RC_0RE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm260: ~halts (TM_from_str "1RB---_1RC1LB_0RD1LE_1LE1RF_0LB0RC_0RE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm261: ~halts (TM_from_str "1RB---_1RC1LB_0RD1LE_1RE1RF_0LB0RC_0RE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm262: ~halts (TM_from_str "1RB1LD_1LC0RE_1RD1LC_0LC0RA_0RD1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm263: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC0RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm264: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC0RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm265: ~halts (TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC0RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm266: ~halts (TM_from_str "1RB1LC_0RC0RE_0LD0RA_1RC1LD_0RC1RF_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm267: ~halts (TM_from_str "1RB1LE_0LC0RC_0RE0RD_1LE---_0LF0RA_1RE1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm268: ~halts (TM_from_str "1RB1LD_1LC0RE_1RD1LC_0LC0RA_0RD1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm269: ~halts (TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm270: ~halts (TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_1LB0RF_0RC1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm271: ~halts (TM_from_str "1RB0LD_1LC1RF_1RA0RD_0RB1LE_1RD0LE_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm272: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm273: ~halts (TM_from_str "1RB1LF_0LC0RC_0RF1RD_1LE---_1RF1LE_0LE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm274: ~halts (TM_from_str "1RB1LE_0LC0RC_0RE1RD_1LE---_0LF0RA_1RE1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm275: ~halts (TM_from_str "1RB1LC_0RC0RE_0LD0RA_1RC1LD_0RC1RF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm276: ~halts (TM_from_str "1RB1LC_0RC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm277: ~halts (TM_from_str "1RB1LD_1LC0RE_1RD1LC_0LC0RA_0RD0RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm278: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm279: ~halts (TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC1RF_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm280: ~halts (TM_from_str "1RB1LC_1RC0RE_0LD0RA_1RC1LD_0RC1RF_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm281: ~halts (TM_from_str "1RB0LE_0RC0LD_1LD1RE_0LA0RA_1RF0LB_0RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm282: ~halts (TM_from_str "1RB0RA_1LC1RA_1LE0LD_1LE0LF_0RB1LC_---0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm283: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD0RE_1LA0LB_0LD0LF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm284: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD1LA_1LA0LB_0LD0LF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm285: ~halts (TM_from_str "1RB1RF_1RC0LD_1LB0RE_1LC0LB_---0RF_1RA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm286: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD0RC_1LA0LB_0LD0LF_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm287: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA1LD_1RA1LF_0LC1LA_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm288: ~halts (TM_from_str "1RB1RC_0LA1LE_1RD0RA_1LB0RA_1LF1LD_---0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm289: ~halts (TM_from_str "1RB0LC_1LC1RD_0LE1LA_0RB1RD_---1LF_0LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm290: ~halts (TM_from_str "1RB0LC_1LC1RD_0LE1LA_0RB1RD_---1LF_0LA0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm291: ~halts (TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1LC1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm292: ~halts (TM_from_str "1RB0LF_0LB1RC_1RD0RF_0LE0RD_0RA1LE_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm293: ~halts (TM_from_str "1RB0LD_1LC1RF_0RA1LC_1LE---_0LC0RE_1RE0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm294: ~halts (TM_from_str "1RB0LE_1RC1RF_0LD0RC_0RA1LD_1LC---_1RC0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm295: ~halts (TM_from_str "1RB0RE_0LC0RB_0RD1LC_1RF0LE_1LB---_1RB1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm296: ~halts (TM_from_str "1RB0LC_1LA1RF_1LD---_0LE0RD_0RA1LE_1RD0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm297: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA1LF_0LB0RE_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm298: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0LF_0LB0RD_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm299: ~halts (TM_from_str "1RB1LE_1LC1RD_0LA1RD_0RB1RD_0LF0LB_---0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm300: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA0LF_0LB0RE_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm301: ~halts (TM_from_str "1RB1LE_0RC0LD_1LD1RB_0LA1LF_0LB0RE_0RE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm302: ~halts (TM_from_str "1RB1LE_1LC1RD_0LA1LD_0RB1RD_0LF0LB_---0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm303: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LB_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm304: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RA_0LA0RE_1RF0RB_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm305: ~halts (TM_from_str "1RB0LE_0RC1LF_1LD1RA_0LA0RB_0RC0LD_---0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm306: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm307: ~halts (TM_from_str "1RB1RE_0RC0LD_1LD1RA_0LA0RF_0LF---_0RB0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm308: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RA_0LA0RE_0RF---_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm309: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RD_0RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm310: ~halts (TM_from_str "1RB0LF_0LC0RD_0LA1RD_0RE---_1LC1RA_0RE0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm311: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LE---_0RF1RF_0LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm312: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF1RF_0LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm313: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm314: ~halts (TM_from_str "1RB0LD_0LC0RF_0LA1RD_0RE0LC_1LC1RA_0RE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm315: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB1RD_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm316: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RD_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm317: ~halts (TM_from_str "1RB0LB_0RC1RE_1LD1RA_0LA0RF_0LF---_0RB0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm318: ~halts (TM_from_str "1RB0LD_0LC0RD_0LA1RD_0RE0RF_1LC1RA_0LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm319: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_0RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm320: ~halts (TM_from_str "1RB0LB_0LC0LF_0RD1RD_0RE---_1LF1RA_0LA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm321: ~halts (TM_from_str "1RB0LE_0RC0RD_1LD1RA_0LA1RF_0RC0LD_0RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm322: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm323: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RD_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm324: ~halts (TM_from_str "1RB0RB_0RC0LD_1LD1RE_0LE---_0RF0LB_0LA1RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm325: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RA_0LA0RE_1RF0RC_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm326: ~halts (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LD_0RD0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm327: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA---_0RF1RD_0LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm328: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD1RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm329: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA1LC_1RB0RF_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm330: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RF_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm331: ~halts (TM_from_str "1RB0LD_1LC0RF_0LA1RD_0RE0LC_1LC1RA_0RE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm332: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm333: ~halts (TM_from_str "1RB0LB_0RC0LD_1LD1RE_0LA---_0RF1RD_0LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm334: ~halts (TM_from_str "1RB1LC_0LC0RD_0LA1RD_0RE0LF_1LC1RA_---0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm335: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC0LA_1LE0LA_1LA0LF_---0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm336: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LA1LF_---1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm337: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LA0LF_---0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm338: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA0LE_1LF0LA_---1RB_1LA1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm339: ~halts (TM_from_str "1RB---_1RC1LB_0LB0RD_1RE1LC_0RA0RF_0RC1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm340: ~halts (TM_from_str "1RB0LE_1LC0RF_0RA0RD_0RB1LB_1LA0LE_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm341: ~halts (TM_from_str "1RB0LC_1LC0RE_1LA1LD_0RA0RF_1RD1RD_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm342: ~halts (TM_from_str "1RB1RD_1LC0RB_0RA1LD_0RE1RB_0LC0LF_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm343: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD0LC_0LB0RE_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm344: ~halts (TM_from_str "1RB0RA_0LB0RC_1RD---_0RE1RA_1RF0LF_1LE1LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm345: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LA0LF_---0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm346: ~halts (TM_from_str "1RB0LC_1LC0RD_1LA0LC_1RE1RE_0RA0RF_0RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm347: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD0LC_0LB1RD_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm348: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD1LF_0LB0RE_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm349: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA1RC_0RB1LF_1RF---_0RA0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm350: ~halts (TM_from_str "1RB0LE_1LC0RF_0RA0RD_0RB1LB_1LA0LD_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm351: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA1RC_0RB0LC_1RF---_1RA0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm352: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA1RC_0RB0LD_1RF---_0RA0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm353: ~halts (TM_from_str "1RB0RD_1RC0LD_1LA1RF_0RC1LE_1RD0LE_0RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm354: ~halts (TM_from_str "1RB0LE_1LC0RF_0RA0RD_0RB1LB_1LA1LC_1RC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm355: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD1LF_0LB1RD_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm356: ~halts (TM_from_str "1RB0LD_0LC0RE_1LA1RC_0RB0LC_1RF---_0RA0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm357: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD0LB_0LB0RE_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm358: ~halts (TM_from_str "1RB1LB_0LC0RC_0RF1RD_1LE---_1RE0RA_0LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm359: ~halts (TM_from_str "1RB1LB_0LC0RC_0RF1RD_1LE---_1RF0RA_0LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm360: ~halts (TM_from_str "1RB0LC_1LA0RE_0RD0LB_0LB1RD_1RF---_0RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm361: ~halts (TM_from_str "1RB1RD_1LC1LC_1LD1LC_1RE1LF_---1RA_0LC0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm362: ~halts (TM_from_str "1RB1RE_0LC0RA_1LD1LC_1RA1LB_1RF1RD_---1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm363: ~halts (TM_from_str "1RB---_0RC0LB_0LD1RC_1LE0RA_0RE1LF_1LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm364: ~halts (TM_from_str "1RB1RD_1LB1RC_1LD1LC_1RE1LF_---1RA_0LC0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm365: ~halts (TM_from_str "1RB1RD_1LC1RC_1LD1LC_1RE1LF_---1RA_0LC0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm366: ~halts (TM_from_str "1RB1RE_1RC1LD_0LD0RF_1LE1LD_1RF1LC_---1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm367: ~halts (TM_from_str "1RB1RD_1LB1LC_1LD1LC_1RE1LF_---1RA_0LC0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm368: ~halts (TM_from_str "1RB1RE_1RC1RD_0LD0RF_1LE1LD_1RF1LC_---1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm369: ~halts (TM_from_str "1RB1LC_1LA0RF_1LD0LF_0RE0LD_0LB1RE_1RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm370: ~halts (TM_from_str "1RB1RE_0LC0RA_1LD1LC_1RA1LB_1RF1RD_---1LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm371: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LD0LE_1LA1RC_---0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm372: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD---_0LD0LA_1RF0RE_1LC0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm373: ~halts (TM_from_str "1RB0RE_0RC1LD_1LD0RA_1LA0LE_0LF0LC_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm374: ~halts (TM_from_str "1RB0RA_0LC1RA_1RF1LD_1LE0LD_1LC0RB_---0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm375: ~halts (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0RF_0LE0LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm376: ~halts (TM_from_str "1RB1RC_0LC0LC_1RE1LD_0LB0LD_0RF---_0RA0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm377: ~halts (TM_from_str "1RB1RC_0LC0RD_1RE1LD_0LB0LD_0RF---_0RA0RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm378: ~halts (TM_from_str "1RB0LF_1RC0RB_0RD0RD_1LE0RF_1LA---_0LC0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm379: ~halts (TM_from_str "1RB1LF_0RC---_0RD0RB_1RE1RA_0LA0LA_0LE0LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm380: ~halts (TM_from_str "1RB1RC_1LC0RB_0LD1LD_1RA1LE_0RF0LE_1RB---") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm381: ~halts (TM_from_str "1RB1RC_1LC0RB_0LD1LD_1RA1LE_---0LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm382: ~halts (TM_from_str "1RB---_1LC0RB_0LE0LD_1RD1LE_1RA1LF_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm383: ~halts (TM_from_str "1RB1RE_1LC0RB_0LD1LD_1RA1LF_---1LD_0RA0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm384: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RA1RA_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm385: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RA0LF_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm386: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF0LF_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm387: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RA1RC_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm388: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF0RD_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm389: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RA0RD_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm390: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RD1RA_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm391: ~halts (TM_from_str "1RB0RE_1LC0RB_0LF1LD_0RA0LD_---0LC_1RA1LD") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm392: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_1RD0LF_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm393: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF1RC_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm394: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF1RA_0RB0LF") c0.
Proof. solve_loop2 5 1000%N. Time Qed.

Lemma tm395: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_0LE1LB_1LF0RF_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm396: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1RA1LA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm397: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA1RE_1LF1LC_0RB0LA_---1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm398: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_0LE1LB_1RA1RE_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm399: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA1RE_0LF1LC_0RB0LA_---1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm400: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA1RE_1LF1LC_0RB0LA_---1LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm401: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1LF1RA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm402: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1LF1LA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm403: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1RE1RA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm404: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1RA1RA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm405: ~halts (TM_from_str "1RB1RA_1LC1RF_---1LD_1LE1LB_1RE1LA_0RA0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm406: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA1RE_0LF1LC_0RB0LA_---0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm408: ~halts (TM_from_str "1RB0LF_1RC1RB_1LD0RE_1LA1LC_0RB0LC_---1LD") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm409: ~halts (TM_from_str "1RB1LF_1RC1RB_1LD0RE_1LA1LC_0RB0LC_---0RE") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm410: ~halts (TM_from_str "1RB1LC_1RC0RF_1RD0LF_1RE---_0LC1RA_0RE1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm411: ~halts (TM_from_str "1RB1LF_1RC1RB_1LD0RE_1LA1LC_0RB0LC_---1RD") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm412: ~halts (TM_from_str "1RB---_0LC1RE_1RA0LD_0RB1LB_1RF1LC_1RC0RD") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm413: ~halts (TM_from_str "1RB0RE_1LC0LA_0RD0LB_---1RA_0RF1RD_1LF0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm414: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD---_0LB0RF_1RB0RF_1LB1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm415: ~halts (TM_from_str "1RB---_1LC0RF_1LD0LC_0LE0LE_1RA0LF_0RD0RE") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm416: ~halts (TM_from_str "1RB0RF_1LC1RF_1RE1LD_0LC0LD_0RB---_0RA1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm417: ~halts (TM_from_str "1RB0RA_1LC1RB_1LF0LD_1LE0LC_1RA1LC_---1LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm418: ~halts (TM_from_str "1RB0LC_1RC0RE_1LD0LE_0LA1RB_0RF0RA_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm419: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD0LF_1LA1RA_0RD1RE_0LB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm420: ~halts (TM_from_str "1RB---_1LC0RD_1RD1LD_1LE0RB_0LF0LA_0RA0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm421: ~halts (TM_from_str "1RB0LE_0RC---_0LD0RB_1RE0LA_0RF0LC_1LC1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm422: ~halts (TM_from_str "1RB1LE_1RC---_1RD0RB_0LA0RA_0LD0LF_0LF0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm423: ~halts (TM_from_str "1RB1LF_1RC---_1RD0RB_0LE0RA_0LA1LD_0LF0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm424: ~halts (TM_from_str "1RB1LA_0RC0RE_1LD1RF_0LA0LD_0RF0RB_---1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm425: ~halts (TM_from_str "1RB0LD_1RC0RB_1LA1RC_1LE0LC_---0LF_1RA1RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm426: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD0RF_0LD0LA_1RF0RB_---0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm427: ~halts (TM_from_str "1RB0RA_1LC1RB_1LF0LD_1LE0LC_1RA1LF_---1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm428: ~halts (TM_from_str "1RB0LA_0LC0RD_1LA1LC_1RB0RE_0RB1RF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm429: ~halts (TM_from_str "1RB1LF_1RC---_0RD0LE_1LE1RD_0LA1RC_0LC1LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm430: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_1RD0LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm431: ~halts (TM_from_str "1RB0LA_1LC0RD_1LA0LC_0RE1RB_1RF0RB_---0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm432: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_1RD0LF_0LB1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm433: ~halts (TM_from_str "1RB---_0RC0LD_1LB1RC_1LE1RB_0RD0LF_0LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm434: ~halts (TM_from_str "1RB1RF_0LC0LD_---1LD_1LE0LD_1RA0RC_1RE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm435: ~halts (TM_from_str "1RB1RA_0LC0RA_0LF1LD_1LE0LC_1LA1RA_---0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm436: ~halts (TM_from_str "1RB0RF_0RC1RE_1LB0LD_0LE1RB_1RF1LC_0RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm437: ~halts (TM_from_str "1RB0RA_1RC1RF_1LD0LC_1RF1LE_1RB0LA_---1RA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm438: ~halts (TM_from_str "1RB0RF_1LC1RE_1LD0LC_1LA0LE_0LA0LA_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm439: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LA0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm440: ~halts (TM_from_str "1RB1RE_0LC0RD_1RA0LD_1LC1LB_0RA0RF_1LB---") c0.
Proof. solve_loop2' 1 6 80000%N. Time Qed.

Lemma tm441: ~halts (TM_from_str "1RB0LC_1RC1RD_1LA0LC_1LE---_0RA0RF_0RB1RE") c0.
Proof. solve_loop2' 2 7 10000%N. Time Qed.

Lemma tm442: ~halts (TM_from_str "1RB0LC_1RC0RD_1LA0LC_1RE---_0RA0RF_0RB---") c0.
Proof. solve_loop2' 2 7 10000%N. Time Qed.

Lemma tm443: ~halts (TM_from_str "1RB0LC_1RC0RD_1LA0LC_1RE0RB_0RA1RF_1LB---") c0.
Proof. solve_loop2' 2 7 10000%N. Time Qed.

Lemma tm444: ~halts (TM_from_str "1RB0LC_1LC0RB_0LE1RD_1LA1LD_0RA1LF_0LA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm445: ~halts (TM_from_str "1RB1LD_1RC1RE_0LA0RF_0LC1LA_0RB0RE_1LD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm446: ~halts (TM_from_str "1RB1LE_1RC0LF_1LD0RE_---1LA_0RB0LA_1RE0LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm447: ~halts (TM_from_str "1RB0LD_1LC1RD_0RD0LC_1RE1LE_1LF0RB_---0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm448: ~halts (TM_from_str "1RB0RA_1LC1RE_1LF0LD_1LE0LC_1RA1LF_---1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm449: ~halts (TM_from_str "1RB0RA_1LC1RE_1LB0LD_1LE0LC_1RA1LF_---1LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm450: ~halts (TM_from_str "1RB1RE_1LC0RA_1LE1LD_0LC1LF_0RB0LA_1RE---") c0.
Proof. solve_loop2' 1 6 80000%N. Time Qed.

Lemma tm451: ~halts (TM_from_str "1RB0LC_1RC0RF_1LD0RA_1LE1LC_1LA0LD_---1RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm453: ~halts (TM_from_str "1RB1LE_0RC1RD_1RD0RF_1LA1RB_0LA0LE_0RD---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm454: ~halts (TM_from_str "1RB---_1RC0RA_1LD1RF_1LE0LD_1LB0LF_0LB0LB") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm455: ~halts (TM_from_str "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RF_0LD---") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm456: ~halts (TM_from_str "1RB---_1RC0LD_1LD1RF_0LE0LD_1RE0RC_1RA0RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm457: ~halts (TM_from_str "1RB0RD_0LC0RA_---1LD_1LA0LE_0LF1LC_1RF0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm458: ~halts (TM_from_str "1RB0LE_0RC1RF_0LD0RA_1LA---_1LF0LE_0LC1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm459: ~halts (TM_from_str "1RB0RA_1LC0RD_1RA1LD_1RC0RE_1LC0LF_1LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm460: ~halts (TM_from_str "1RB0RC_1RC1RF_1LD1RA_0LE0LD_1RE0RC_---1LD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm461: ~halts (TM_from_str "1RB1LE_1RC0LF_1LD0RC_0LA1LA_1LD0LB_---0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm462: ~halts (TM_from_str "1RB1LE_0RC0RD_1LD---_0LA1RF_1LA0LE_1RD0RF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm463: ~halts (TM_from_str "1RB1LF_1LC0RD_1RD1LD_1LE0RB_0RA0LF_0LE---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm464: ~halts (TM_from_str "1RB1LF_1RC---_1LD0RC_0LA1LE_0LF0RE_0RB0LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm465: ~halts (TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LE0RE_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm466: ~halts (TM_from_str "1RB0RA_1LC0RA_1RA0LD_1LE0RE_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm467: ~halts (TM_from_str "1RB0RA_1LC0RA_1RA0LD_1LE1LC_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm468: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD0RA_1LA0LE_1LF---_0LB0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm469: ~halts (TM_from_str "1RB1RE_1LC0RA_1RA0LD_1LE1LC_0LB0LF_0LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm470: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD1RF_1LA0LE_1LF---_0LB0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm471: ~halts (TM_from_str "1RB---_1RC1LE_0RD0LF_1LA0RF_0LC0LB_0LB0LA") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm472: ~halts (TM_from_str "1RB---_1RC1LF_0RD0LE_1LE0RE_0LB0LA_0LC0LB") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm473: ~halts (TM_from_str "1RB1LE_1RC0RB_1RD0RE_1LA0LF_0RD0RD_1LD---") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm474: ~halts (TM_from_str "1RB0RD_0RC1RF_1RD0LE_1RE0RA_1LC0LE_1LD---") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm475: ~halts (TM_from_str "1RB---_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RD---") c0.
Proof. solve_loop2' 2 7 40000%N. Time Qed.

Lemma tm476: ~halts (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA0LF_0RA0LB_---1LC") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm477: ~halts (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA1LF_0RA0LB_---1RC") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm478: ~halts (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA1LF_0RA0LB_---0RE") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm479: ~halts (TM_from_str "1RB1LE_1RC0LF_1LD0RF_0RB1LA_1LC---_0LD1LB") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm480: ~halts (TM_from_str "1RB0LE_1RC1RA_1LD0RF_1LA1LD_0LD0RA_---1RB") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm481: ~halts (TM_from_str "1RB0LE_1RC1RA_1LD1RF_1LA1LD_0LD0RA_---1LB") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm482: ~halts (TM_from_str "1RB0LE_1RC1RA_1LD1RF_1LA1LD_0LD0RA_---0LE") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm483: ~halts (TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LC1LE_0RF0RC_---0LB") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm484: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LA1LE_0RF0RA_---0LC") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

