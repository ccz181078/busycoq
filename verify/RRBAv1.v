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
    apply (decide_loop2_spec' _ (min_b,16%nat) n_skip k T);
    native_cast_no_check (eq_refl true)
  end.
Ltac solve_loop2''' min_b min_d n_skip k T :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    apply (decide_loop2_spec' _ (min_b,min_d) n_skip k T);
    native_cast_no_check (eq_refl true)
  end.
Ltac solve_loop2' n_skip k T := solve_loop2'' O n_skip k T.
Ltac solve_loop2 k T := solve_loop2' O k T.

Close Scope sym.

Lemma tm1: ~halts (TM_from_str "1RB---_1RC1LD_0LB0RC_0LE1LE_0LA1RF_1LB0RF") c0.
Proof. solve_loop2 2 1500%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB1LC_0LA0RB_0LD1LD_0LE1RF_1RA---_1LA0RF") c0.
Proof. solve_loop2 2 1500%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1RE_0RC1RA_1LD0LC_0RA0LD_0RF1LC_1LC---") c0.
Proof. solve_loop2 3 2500%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB0RA_0LC0RB_1LF1LD_0LE1RA_1RA---_0LA1LC") c0.
Proof. solve_loop2 3 2500%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1LD_1RC1LC_1LA1RE_0LC0RE_0RF0RB_---0RD") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0LC_1LC1RA_1RF0LD_0RA1LE_1LF1LC_---0RB") c0.
Proof. solve_loop2 7 1500%N. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1LC_0LA0RD_1LA0RB_1RF1RE_1LF1RB_---0LC") c0.
Proof. solve_loop2 7 1500%N. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB0LC_1LC1RA_0LF0LD_1RE1LE_0RB1LC_---0RA") c0.
Proof. solve_loop2 7 1500%N. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1RC0LF_---1LD") c0.
Proof. solve_loop2 2 4000%N. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB0RC_1RC1RA_0LD0LE_0RA1LC_1LC0LF_---1LD") c0.
Proof. solve_loop2 2 4000%N. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB0LF_0LC0LA_0RD1LB_1RE0RD_1RB1RD_---1LC") c0.
Proof. solve_loop2 2 4000%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB0RF_0RC0RA_0LD1RB_1LE0LD_1LB1LD_---1RC") c0.
Proof. solve_loop2 2 4000%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB1RD_0LC1RF_0LE1RD_1LE0RD_1LB1LA_---1RD") c0.
Proof. solve_loop2 5 4000%N. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB1LA_1RC1RE_1LD0LA_---1LC_1LC0RF_0LA0RB") c0.
Proof. solve_loop2 5 4000%N. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0LB_1LC1LB_0LE0RD_0RB1RD_---0LF_1RA0LA") c0.
Proof. solve_loop2 1 1000%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0LB_1RC0LC_1LD1LC_0LF0RE_0RC1RE_---0LA") c0.
Proof. solve_loop2 1 1000%N. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0LB_1RC1LD_1RD0RF_1LE1LD_---0RC_1LF0LA") c0.
Proof. solve_loop2 1 1500%N. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LB_1LC0RF_0LD1LB_1RD0RE_0RA0LA_---0RD") c0.
Proof. solve_loop2 1 2000%N. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LD_0LC1RE_1RB0RB") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB---_1LC0RF_0RA0LD_1LE1LD_0LC1RE_0LC0RB") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB1RF_1LC0RE_---0LD_1LA1LD_1RB0RB_0LC1RF") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RB_1LC0RA_---0LD_1LE1LD_0LF1RE_0RA0LD") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB1LA_1LA0RC_1LD0RB_1LE---_1LF0LB_0LF1RD") c0.
Proof. solve_loop2 6 2000%N. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB0LE_0LC---_1LA0RD_1RC0RC_1LF1LE_0LA1RF") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB0RF_1LC0RA_0RA0LD_1LE1LD_0LC1RE_---0RA") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB---_0RC1LB_0RD0RE_1LD0LE_0LA1LF_0RD0LB") c0.
Proof. solve_loop2 1 2000%N. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0LD_0RC---_1LD0LC_0RE1LC_1LA1RF_1RE0RF") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB0RF_1LC---_0LC1LD_1LE1RD_1RA0LD_1LB0RA") c0.
Proof. solve_loop2 5 1500%N. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB1RA_1RC---_0RD1LC_1LE0RA_0LF0LE_0RA1RD") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB1RE_1LB0LC_1RD0LF_1RA---_1RF0RA_1LB0RD") c0.
Proof. solve_loop2 5 1500%N. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB1RA_1LC0RE_0RD1LD_1LE0LD_0RF0LC_---1RA") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB1RA_1LC0RF_---1LD_1LE0LD_0RA0LC_0RA1RA") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB1RA_1LC0RF_---1LD_1LE0LD_0RA0LC_0RA1LE") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB1RA_1LC0RF_---1LD_1LE0LD_0RA0LC_0RA1LF") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB1RA_1LC0RF_---1LD_1LE0LD_0RF0LC_0RA1RA") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB1RA_1LC0RF_---1LD_1LE0LD_0RF0LC_0RA1LF") c0.
Proof. solve_loop2 3 1500%N. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB1RF_1LC---_1RF0LD_1LE1LD_0LC1RE_0RA0RF") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB1RF_1LC---_1LF0LD_1LE1LD_0LC1RE_0RA0RF") c0.
Proof. solve_loop2 4 1000%N. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA0RF_1LD---") c0.
Proof. solve_loop2 5 3000%N. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB0RF_1LC1RA_1LD0LC_0LE0LA_1RF---_1RA0RC") c0.
Proof. solve_loop2 5 3000%N. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1RB---_1RA0RC") c0.
Proof. solve_loop2 5 3000%N. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB---_1RC1LB_1LD0RB_1LE0LD_1RF1LD_1RA0RF") c0.
Proof. solve_loop2' 1 8 8000%N. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB0RF_1LC1RB_1LF1LD_1LE0LD_1RA---_1LB0RA") c0.
Proof. solve_loop2 6 1500%N. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB---_0LC1RF_1LE0RD_0RB1LE_1RD0LE_0RC1RA") c0.
Proof. solve_loop2 7 3000%N. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB---_1LC1LF_1RD0LB_1RA1RE_0RC0RE_1RB1LB") c0.
Proof. solve_loop2' 1 5 2000%N. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB1LB_1LC1LA_1RD0LB_1RA1RE_0RC0RF_---0RE") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB0LD_1RC1RF_1RD---_1LA1LE_1LD0RD_0RA0RF") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB1RF_1RC---_1LD1LE_1RA0LC_1LC1LC_0RD0RF") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB1LB_1LC1LA_1RD0LB_0RF1RE_0RC0RE_0RA---") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB---_1RC1RA_1LD0RB_0RC0LE_1LF1LD_1RB0RD") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB0LC_0LA0RD_1LA1LE_1RE1RB_1LC0LF_---0RD") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB0LC_0LA0RD_1LA1LF_1RE1RB_1LC0LB_1LC---") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB0LD_0LC0RE_---0LD_1LA1LF_1RF1RB_1LD0LB") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_---0LE_1LA1LF_0RC0LE") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_0RF0LE_1LA1LD_---0RB") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LE1LF_1RA0RC_0RB0LD") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LE1LF_1RA0RF_0RB0LD") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB0RF_1RC1RA_1LD0RB_---0LE_1LA1LF_0RC0LE") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB0RF_1RC1RA_1LD0RB_---1RE_1LA1LF_0RC0LE") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB0RF_1RC1RA_1LD0RB_0RC0LE_1LA1LD_---0LE") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB1RF_1LC0RA_---1RD_1LF1LE_0RB0LD_1RA0RE") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_---0LE_1LA0LF_1RA1RC") c0.
Proof. solve_loop2' 1 6 8000%N. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_1RF0LE_1LA1LD_---0RC") c0.
Proof. solve_loop2' 1 5 3000%N. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---1RA") c0.
Proof. solve_loop2' 1 6 8000%N. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---0LA") c0.
Proof. solve_loop2' 1 6 8000%N. Time Qed.

Lemma tm66: ~halts (TM_from_str "1RB1RE_1LC0LE_1LD1LB_1RE0LC_1LF0RA_---0LD") c0.
Proof. solve_loop2 4 2000%N. Time Qed.

Lemma tm67: ~halts (TM_from_str "1RB0RA_1RC0RD_1RD---_1LE0LF_1RA0RF_1LD1LF") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm68: ~halts (TM_from_str "1RB0RF_1LC0LF_1LD0LC_1LE0LA_1LA---_1RA1RF") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm69: ~halts (TM_from_str "1RB0RA_1RC0RD_1RD---_1LE0LF_1RA1LD_1LD1LF") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm70: ~halts (TM_from_str "1RB0RC_1RC---_1LD0LE_1RF0RE_1LC1LE_1RA0RF") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm71: ~halts (TM_from_str "1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LB---") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm72: ~halts (TM_from_str "1RB0RC_1RC---_1LD0LE_1RF1LC_1LC1LE_1RA0RF") c0.
Proof. solve_loop2 4 8000%N. Time Qed.

Lemma tm73: ~halts (TM_from_str "1RB1RF_1LC0RA_---0LD_1LE1LC_1LA0RC_1RA1RF") c0.
Proof. solve_loop2' 1 5 6000%N. Time Qed.

Lemma tm74: ~halts (TM_from_str "1RB0RF_0RC1RB_1LD0RA_0LE0LA_1RC1LE_0LD---") c0.
Proof. solve_loop2' 1 5 4000%N. Time Qed.

Lemma tm75: ~halts (TM_from_str "1RB---_1LC0RF_0LE1LD_0RE1RB_0RA0LB_1RD0RF") c0.
Proof. solve_loop2 7 8000%N. Time Qed.

Lemma tm76: ~halts (TM_from_str "1RB---_1RC1LB_0RD1RF_1LE0RD_0LE0LB_1RA0RC") c0.
Proof. solve_loop2 4 6000%N. Time Qed.

Lemma tm77: ~halts (TM_from_str "1RB0RD_1RC---_1RD1LC_0RE1RA_1LF0RE_0LF0LC") c0.
Proof. solve_loop2 4 6000%N. Time Qed.

Lemma tm78: ~halts (TM_from_str "1RB1RC_1LC0RF_---1LD_1LE0LD_0RF0RB_1RA1RF") c0.
Proof. solve_loop2 5 10000%N. Time Qed.

Lemma tm79: ~halts (TM_from_str "1RB1RA_1RC1RD_1LD0RA_---1LE_1LF0LE_0RA0RC") c0.
Proof. solve_loop2 5 10000%N. Time Qed.

Lemma tm80: ~halts (TM_from_str "1RB0LB_0RC0RF_1RD1RC_1LE0RF_0LA0LE_0RD---") c0.
Proof. solve_loop2 5 8000%N. Time Qed.

Lemma tm81: ~halts (TM_from_str "1RB0LF_0RC0RB_1LD0RD_0LE0LF_1LA1LE_0LA---") c0.
Proof. solve_loop2 5 6000%N. Time Qed.

Lemma tm82: ~halts (TM_from_str "1RB0RC_1LC1RA_0RA1LD_0LE---_1LF1LE_0RB0RE") c0.
Proof. solve_loop2' 1 5 6000%N. Time Qed.

Lemma tm83: ~halts (TM_from_str "1RB0RC_1LC1RA_0RA1LD_0LE---_1LF1LE_0RB1LF") c0.
Proof. solve_loop2' 1 5 10000%N. Time Qed.

Lemma tm84: ~halts (TM_from_str "1RB---_1RC0LB_1RD0RC_0LE1RC_1LB1LF_1LA1LE") c0.
Proof. solve_loop2 5 12000%N. Time Qed.

Lemma tm85: ~halts (TM_from_str "1RB1LB_1LA0RC_1LD0RB_0LE0LF_0RA1LF_0LD---") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm86: ~halts (TM_from_str "1RB1RF_1LC---_1LD0RC_1LE0LD_0RF1LD_1RC1RA") c0.
Proof. solve_loop2 4 20000%N. Time Qed.

Lemma tm87: ~halts (TM_from_str "1RB---_1LC0RC_0RD0LC_0LE0RA_1LF1LC_1RD0LF") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm88: ~halts (TM_from_str "1RB0LA_1RC0RB_0LD1RB_1LA1LE_0LF1LD_0LA---") c0.
Proof. solve_loop2 5 12000%N. Time Qed.

Lemma tm89: ~halts (TM_from_str "1RB0RA_0LC1RA_1LF1LD_0LE1LC_0LF---_1RA0LF") c0.
Proof. solve_loop2 6 20000%N. Time Qed.

Lemma tm90: ~halts (TM_from_str "1RB0RA_0LC1RA_1LF1LD_1LE1LC_1RF---_1RA0LF") c0.
Proof. solve_loop2 6 20000%N. Time Qed.

Lemma tm91: ~halts (TM_from_str "1RB0LA_1RC1LE_0RD0RC_0LE0RD_1LF---_0LA1LB") c0.
Proof. solve_loop2' 1 5 12000%N. Time Qed.

Lemma tm92: ~halts (TM_from_str "1RB---_0RC1RD_1LD0RC_1LE1RA_0LF0LE_0RA0LF") c0.
Proof. solve_loop2' 1 5 20000%N. Time Qed.

Lemma tm93: ~halts (TM_from_str "1RB0LE_1LC1RA_0LF0LD_0RD1LA_1RD0LC_0LE---") c0.
Proof. solve_loop2' 1 6 12000%N. Time Qed.

Lemma tm94: ~halts (TM_from_str "1RB1LF_0RC0RE_0RD---_1LE0RB_0LE1RF_1LA0RD") c0.
Proof. solve_loop2 5 12000%N. Time Qed.

Lemma tm95: ~halts (TM_from_str "1RB---_1LC0RF_1RE0LD_0LC1RB_1RA0RC_1LC0RD") c0.
Proof. solve_loop2' 1 6 6000%N. Time Qed.

Lemma tm96: ~halts (TM_from_str "1RB0LC_1LA0RD_1LA1LE_1RE1RB_1LC0LF_---0RD") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm97: ~halts (TM_from_str "1RB0LC_1LA0RD_1LA1LF_1RE1RB_1LC0LB_1LC---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm98: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD1LA_1RE0RF_1RB1RD_---0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm99: ~halts (TM_from_str "1RB0LD_0LC0RE_---1RD_1LA1LF_1RF1RB_1LD0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm100: ~halts (TM_from_str "1RB0LD_1LC0RE_---0LD_1LA1LF_1RF1RB_1LD0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm101: ~halts (TM_from_str "1RB0LD_1LC0RF_---0LD_1LE1LA_1RF0RC_1RB1RE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm102: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_---0LE_1LA1LF_1RC0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm103: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_0RF0LE_1LA1LD_---1LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm104: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_1RF0LE_1LA1LD_---0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm105: ~halts (TM_from_str "1RB0RD_1RC1RF_1LD0RB_1RC0LE_1LA1LD_1RB---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm106: ~halts (TM_from_str "1RB1RE_1LC0RA_0RF0LD_1LE1LC_1RA0RC_---1LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm107: ~halts (TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm108: ~halts (TM_from_str "1RB1RE_1LC0RA_1RF0LD_1LE1LC_1RA0RC_---0RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm109: ~halts (TM_from_str "1RB1RE_1LC0LE_1LD1LB_1RE0LC_0LF0RA_---1RC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm110: ~halts (TM_from_str "1RB1RE_1LC0LE_1LD1LB_1RE0LC_1LF0RA_---0LC") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm111: ~halts (TM_from_str "1RB1RE_1LC0LF_1LD1LB_1RE0LC_1LD0RA_---0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm112: ~halts (TM_from_str "1RB0RF_1RC1RA_1LD0RB_1RC0LE_1LA1LD_---0LE") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm113: ~halts (TM_from_str "1RB1RF_1LC0RA_1RB0LD_1LE1LC_1RA0RC_1RA---") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm114: ~halts (TM_from_str "1RB1RF_1LC0LE_1LD1LB_1RE0LC_---0RA_1LD0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm115: ~halts (TM_from_str "1RB1RF_1LC0LF_1LE1LD_1LC---_1RF0LC_1LE0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm116: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LF_1RF1RB_1LD0LB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm117: ~halts (TM_from_str "1RB0LD_1LC0RF_---0RD_1LA1LE_1LD0LB_1RE1RB") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm118: ~halts (TM_from_str "1RB1RD_1RC0RE_1RD1RB_1LE0RC_---0LF_1LB0LA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm119: ~halts (TM_from_str "1RB0LD_1LC1LF_1RD0LB_---0RE_1RA1RD_1LB1LF") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm120: ~halts (TM_from_str "1RB---_1LC0LD_1RE0RD_1LB1LD_1RF0RE_1RA0RB") c0.
Proof. solve_loop2 4 10000%N. Time Qed.

Lemma tm121: ~halts (TM_from_str "1RB---_1LC0LF_1RD1LB_1RE0RD_1RA0RB_1LB1LF") c0.
Proof. solve_loop2 4 10000%N. Time Qed.

Lemma tm122: ~halts (TM_from_str "1RB1RF_1RC0LF_1LD1LE_1RF0LC_1LC1LE_---0RA") c0.
Proof. solve_loop2' 1 6 10000%N. Time Qed.

Lemma tm123: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RB_0LF0LE_1LA1LD_0LE---") c0.
Proof. solve_loop2' 1 5 12000%N. Time Qed.

Lemma tm124: ~halts (TM_from_str "1RB---_0RC1RD_0LD1RF_1LE0RB_1RC0LB_1LD1RA") c0.
Proof. solve_loop2' 1 5 10000%N. Time Qed.

Lemma tm125: ~halts (TM_from_str "1RB0RA_1RC0LF_1LD0RC_1LE0LD_0LA1LF_---1LC") c0.
Proof. solve_loop2' 1 5 20000%N. Time Qed.

Lemma tm126: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LE_0RF0LC_1LB0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm127: ~halts (TM_from_str "1RB---_1RC0RF_1LD1LB_1RE0LD_1LB0RA_0RE0LC") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm128: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LC_0RF0LC_1LB0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm129: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LC_0RF0LE_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm130: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LE_0RF0LC_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm131: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LE_0RF0LE_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm132: ~halts (TM_from_str "1RB---_1RC0RE_1LD1LB_1RF0LC_0RF0LC_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm133: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RF0LC_0RF1LD_1LB0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm134: ~halts (TM_from_str "1RB0LA_0LC1RA_0LF1RD_1LC1RE_0RD0RE_---1LA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm135: ~halts (TM_from_str "1RB0LA_1LC1RA_0LF1RD_1LC1RE_0RD0RE_---1LA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm136: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RF0LC_0RF1LC_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm137: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RF0LC_0RF0RF_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm138: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RF0LC_0RF1LD_0LC0RA") c0.
Proof. solve_loop2' 2 6 60000%N. Time Qed.

Lemma tm139: ~halts (TM_from_str "1RB0LD_1RC0RB_1RD1RF_1LA0LE_0LC1LD_1LB---") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm140: ~halts (TM_from_str "1RB1RE_0RC0RF_1LD1RB_0LD1LE_1RA0LE_0RC---") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm141: ~halts (TM_from_str "1RB---_0RC0RF_1RD0LF_0LE0RA_1LC1LE_0RD1LB") c0.
Proof. solve_loop2' 1 6 60000%N. Time Qed.

Lemma tm142: ~halts (TM_from_str "1RB---_0RC0RF_1RD0LF_0LE0RA_1LC1LE_0RD0LE") c0.
Proof. solve_loop2' 1 6 60000%N. Time Qed.

Lemma tm143: ~halts (TM_from_str "1RB---_0RC0RF_1RD0LF_0LE0RA_1LC1LE_0RD0LF") c0.
Proof. solve_loop2' 1 6 60000%N. Time Qed.

Lemma tm144: ~halts (TM_from_str "1RB0LA_1RC0RB_0RD1RF_1LE0LD_1LA0RF_---1RA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm145: ~halts (TM_from_str "1RB0LD_1RC1RB_1RD0RF_1LA0LE_0LC1LD_0RB---") c0.
Proof. solve_loop2' 2 6 40000%N. Time Qed.

Lemma tm146: ~halts (TM_from_str "1RB0LF_1LC0RB_1LD0LC_0LE1LF_1RA0RE_---1LB") c0.
Proof. solve_loop2' 1 5 20000%N. Time Qed.

Lemma tm147: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RF0LC_0RF0RD_0LC0RA") c0.
Proof. solve_loop2' 2 6 40000%N. Time Qed.

Lemma tm148: ~halts (TM_from_str "1RB0RA_0RC1RF_1LD0LC_1LE0RF_1RA0LE_---1RE") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm149: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD0RC_1LE1RC_0LF---_---1LA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm150: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD0RE_1LE1RC_0LF---_0RC1LA") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm151: ~halts (TM_from_str "1RB0LA_1RC1RA_0RD0RF_1LE1RC_0LE1LA_0RD---") c0.
Proof. solve_loop2' 1 6 20000%N. Time Qed.

Lemma tm152: ~halts (TM_from_str "1RB0LE_1LC0RE_0RA1LD_1RA1LA_0LC1RF_0LD---") c0.
Proof. solve_loop2' 1 6 40000%N. Time Qed.

Lemma tm153: ~halts (TM_from_str "1RB0LD_1RC0RB_1RD0RF_1LA0LE_0LC1LD_0RB---") c0.
Proof. solve_loop2' 1 5 40000%N. Time Qed.

Lemma tm154: ~halts (TM_from_str "1RB0RF_0RC0LD_1RD0LE_1LB1LC_1RF0RA_1RA---") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm155: ~halts (TM_from_str "1RB0LD_1LC1LA_0RA0LB_1RE0RF_1RF---_1RC0RE") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm156: ~halts (TM_from_str "1RB0RF_0RC0LD_1RD0LE_1LB1LC_1RF1RA_1RA---") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm157: ~halts (TM_from_str "1RB1RC_1RC---_1RD0RB_0RE0LF_1RF0LA_1LD1LE") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm158: ~halts (TM_from_str "1RB---_1RC0RA_0RD0LE_1RE0LF_1LC1LD_1RA0RB") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm159: ~halts (TM_from_str "1RB0LD_1LC1LA_0RA0LB_1RE1RF_1RF---_1RC0RE") c0.
Proof. solve_loop2'' 7 1 8 40000%N. Time Qed.

Lemma tm160: ~halts (TM_from_str "1RB1RD_0RC1LF_0RD1RF_1LE1RA_1RB0LE_---1LD") c0.
Proof. solve_loop2'' 6 1 8 40000%N. Time Qed.

Lemma tm161: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD1RD_1RE---_0LF1LA_1RA1LF") c0.
Proof. solve_loop2' 2 7 20000%N. Time Qed.

Lemma tm162: ~halts (TM_from_str "1RB1LD_0RC---_0LD1RE_0LA0LB_1LF0RE_1LD1LE") c0.
Proof. solve_loop2' 1 5 40000%N. Time Qed.

Lemma tm163: ~halts (TM_from_str "1RB1RF_0RC0RB_1LD1RB_0LE---_1LC1LF_1RA0LF") c0.
Proof. solve_loop2' 1 5 40000%N. Time Qed.

Lemma tm164: ~halts (TM_from_str "1RB0LA_1RC1LB_1RD1LA_0RE1RF_1LA---_1RE0RD") c0.
Proof. solve_loop2''' 8 8 1 5 10000%N. Time Qed.

Lemma tm165: ~halts (TM_from_str "1RB0LA_1RC1LB_1RD1LA_1RE1RF_1LB---_0RE0RD") c0.
Proof. solve_loop2''' 8 8 1 5 10000%N. Time Qed.

Lemma tm166: ~halts (TM_from_str "1RB1RE_1LC0RA_0LF0LD_1LE1LC_1RA0RC_0LD---") c0.
Proof. solve_loop2''' 8 8 1 5 20000%N. Time Qed.

Lemma tm167: ~halts (TM_from_str "1RB0LF_0RC0RD_0RD---_1RE1RB_1LF0LB_1LA1LE") c0.
Proof. solve_loop2''' 8 8 1 5 20000%N. Time Qed.

