From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec default_config T);
  [ apply Config_WF_simple; reflexivity
  | vm_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T 3000000%N)
  end.


Lemma nonhalt1: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1RA_0LC1RE_0RA1LD_1LC0LB_0RA0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0LE_1LC0RD_1LA1LB_1RC0RA_1RD0LF_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1LF_0RC---_1LD1RE_0RE1RD_1RF1RC_1LA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RD_0LC0LB_1RF1RD_0RE---_1LC0RC_0RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB---_1RC1RF_0RD0RE_1LE0RB_0LF0RF_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0RA_0LB1LC_1LD1LE_0LE1RB_1RA1LF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0LF_1RC0RA_1LD0RB_0LE0LC_1LA1RE_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB1RA_0LC1RE_0RA1LD_1LC0LB_0LF0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB0RC_1LC0RB_1LD0LD_1RE0LB_1RB0RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0RC_1LC1LB_1RD0LB_---1RE_1RF0RF_0RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB0LE_0RC0LC_1LD0RA_1LE---_1LF1LC_0LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB1LE_0RC1LA_1LD0RD_0LA0RD_0LB0LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB0LB_0RC1LD_1LC1RA_1RE0LF_---0RF_0LA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB0LA_1RC0RC_1LD0RA_1LA0LE_---0LF_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1RE_0RC0RD_1LD0RA_0LE0RE_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB1LE_0RC1LA_1LD0RD_0LA1LB_0LB0LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB1RE_0RC1LD_1RD0RE_0LA0LD_0RF---_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD0RF_1LA0LD_1RA0LC_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB0LB_1LC1LF_0LE1RD_0RB0RD_1LD0LF_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB0RB_1LC0RF_1RE0LD_1LC1LD_---1RA_1RD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB0LC_1RC0RE_1LD0RC_1LA0LA_---0RF_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB---_1RC0LE_0RD0RB_1LE1RA_0LF0RA_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LE_1RC---_1RD1RA_0RE0RF_1LF0RC_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB0RC_1LC1LB_1RD0LB_---1RE_1RF0RF_1LC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB1RD_1LC0LE_1LD1LB_1RE0LA_1LF0RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB0RE_1LC0RB_1LD0LD_1RA0LB_---0RF_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD1LA_1RF1RE_0RB1LE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB1RE_1LC1LD_1RD0LB_0LC0RA_1RB1RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD1LA_1RF1LE_0RB1LE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB0RC_0LC0RB_0RA1LD_0LE---_1LF0LF_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0RB_1RC1RE_1LD0LE_0RE0LD_0LC1RF_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB1LD_1RC1LE_1LA0RB_0LF0LA_0RD1LE_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB0LE_1RC0RB_1RD0RF_1LE0RA_1LA0LE_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.


