From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec config_limited_repeater_size T);
  [ apply Config_WF_simple; reflexivity
  | vm_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T 1000000%N)
  end.

Lemma nonhalt1: ~halts (TM_from_str "1RB1RF_0RC1RD_0LD0RA_1LE0LC_1LA0LB_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0LC_1LC---_1LD1LC_0RE1RD_1LF1RF_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1LE_0RC1RD_1RD---_0LA0LF_1LF1RD_0LD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB1LF_1LC0RC_0LE1RD_0RB1RD_---0LA_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0RD_1LF1LE_0LD---_0LB0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0RE_1RC0RD_1LD1LF_0LE1LA_0RA0LC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB---_0RC0LE_1RD1RC_1LB1RA_0LF1LB_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0RF_1RC1RF_0LD0RD_1LA0RE_1LC---_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB1LA_1LC0RE_1LF1LD_0LE0LC_1RA1RE_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB1LD_1RC0RC_1LD0RE_0LB1RB_1LF0LA_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB1LB_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB0RD_1RC0RC_1LD0RF_---0LE_1LB1LE_0RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA---_0RC0RF_0LA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB0RA_1LC0RF_0RD0LB_0RF0LE_0LD---_1RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB---_1RC1RB_0LD1LC_1RF1LE_1LA0LD_0RF0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB1RF_0RC1RD_0LD0RA_1LE0LC_1LA0LB_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB0RE_1RC0RD_1LD1LF_0LE1LA_0RA0LC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB1RD_1LC0RD_---1LA_1LE1RA_0LE0LF_0RC1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1LB_0LC1LE_---1LD_1RE1LA_1LF0RF_1RE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB1RF_0LC0RC_1LE0RD_1LB---_1RA0RF_0RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB---_0RC0LC_1RD0LA_1LE0LF_1LB1LF_0LD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB1RE_1RF0RC_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB1RF_0RC0RB_1RD0LE_1RE0LA_1LC0LE_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB0RF_0RC1RD_0LD0RA_1LE0LC_1LA0LB_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB0RE_1RC0RD_1LD0LF_0LE1LA_0RA0LC_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0LE_0LC0RA_0LE0RD_0RC---_1LF0RF_1LA0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB0RC_1LC1LE_1RA0LD_1LE0LF_0LC0RA_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB1RF_0RC1RD_0LD0RA_1LE1LA_1LA0LB_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0LF_1LC0LD_1LE1LD_0LB0RE_0RA0LA_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB0RA_1LC1RB_1RF0LD_1LA1LE_0LB1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB1LC_0RC1RE_1LD1LF_1LE0RA_0LA0LD_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB1RE_1RC1LC_1LD0RE_0LE0LB_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA0RF_0RC0RD_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB0LB_1LA1LC_1LA1RD_1LE1RE_0RF1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB1RA_1LC1RF_0RA0LD_0LE1LC_1RE0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LC_1LA1RD_1RF1RB_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB0RF_0RC0RF_0LD0RA_1LE---_1LA0LD_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_0LA0LE_1LF1LD_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB1LF_1LC0RD_0LE1RD_0RB1RD_---0LA_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB0LB_1RC0RB_1LD0RA_0RE0LC_0RA0LF_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB0RF_0RC1RD_0LD0RA_1LE1LA_1LA0LB_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB1RB_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB1RF_1RC0LD_0RD0RB_1LE1RA_0LA1LC_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA1RC_0RD0RF_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB1RE_1LC0LE_1RD0LB_1RB0RA_1RF0RC_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB1RC_1RC0RD_1LD1LE_0LF1LA_---0RF_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_1RE1RD_1LF0RE_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB---_1RC0RA_1LD0LE_0LF0LE_1RA1LD_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB1LC_0RC0LD_0RD0RB_1LE1RA_0LF1LC_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB---_0LC0LE_1RF1LD_1LE0LF_0LB0RC_0RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB1LA_1RC0RD_1LC0LA_1RE1RD_1LF0RE_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB1RC_1RC0RD_1LD0LE_0LF1LA_---1LD_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB1LB_1LC0RE_0RC0LD_1LA---_1RA1RF_0RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB1LB_1LC0RE_0RC0LD_1LA---_0RE1RF_0RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.



