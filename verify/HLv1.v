From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Definition T0:N := 0.
Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec (config_arithseq T0) T);
  [ apply Config_WF_simple; reflexivity
  | vm_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T 3000000%N)
  end.

Lemma nonhalt1: ~halts (TM_from_str "1RB0RA_1LC0RD_0LE0LD_1RA0LB_1LA1LF_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1RF_1LC0LB_1RE0LD_1LB0RC_0RA0RD_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0LC_1RC0RB_1LD0RA_0LE0LA_1LB1LF_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LE_0RC0RE_1RD1RF_1LA0LD_1LD0RA_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB---_1RC0LF_0RD0RF_1RE1RA_1LB0LE_1LE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RE_1RC0RE_1LD0RB_1LA0LE_0RC1LF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0RA_1LC0RA_1LD0LB_1RE0LC_1RF1RE_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0RF_1RC1RC_0LD0RE_1LA1LD_0RA1RE_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB0RA_1LC1RC_1LE1RD_---0LE_1RF1LF_0LB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.


