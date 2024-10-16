From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Ltac solve_hlin_nonhalt_T T T0 bsz :=
  apply (decide_hlin_nonhalt_spec _ (config_arithseq_fixed_block_size T0 bsz) T);
  vm_cast_no_check (eq_refl true).

Ltac solve_hlin_nonhalt bsz :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T 500000%N 0%N bsz)
  end.




Lemma nonhalt3: ~halts (TM_from_str "1RB0RB_1RC1LD_1LB0RA_0RF1RE_1LB0RD_---0LC") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0RB_1RC1LD_1LB0RA_0RF1RE_1LB0RD_---0LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0RB_1RC1LD_0LD0RA_0RF1RE_1LB0RD_---0LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RB_1RC1LE_1LD0RA_1LB0RE_0RF1RD_---0LD") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0RB_1RC1LD_1LB0RA_0RF1RE_1LF0RD_---0LC") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB0RE_1LC1LD_---0LD_1RA1LB_1RA0LF_1RF1LE") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0LD_1RC0RF_1RD1RB_1LA0RE_1LE1RD_1RC---") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB1RE_1LB1RC_1LD0RB_1RE0LC_1RA0RF_1RA---") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB1RF_1LB1RC_1LD0RB_1RE0LC_---0RF_1RA0RD") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB0RB_1RC0LD_1LB0RA_1LB1RE_0RF---_0RB1RD") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB0RB_1RC0LE_0LD0RA_0RB1RE_1LB1RF_0RD---") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB0LE_1RC0LD_1LB0RA_1LB1RE_0RF---_0RB1RD") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB0LF_1RC0LE_0LD0RA_0RB1RE_1LB1RF_0RD---") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB0RC_0LA0RE_1LD0LC_1LA1RF_0RF1RA_---1RB") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB1LA_0LC0RF_---0LD_1LE0RC_1RF1LD_1RD0RA") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB0RA_0RC0RE_0LD1LA_0LE1LB_1RA0RF_1LC---") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB0LB_0RC0LD_1LA0RF_---0LE_1RE0RF_1LC0RA") c0.
Proof. solve_hlin_nonhalt 4. Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB0RF_0LC1RA_1LE0RD_0RB---_0LF0LC_1LD1RC") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB1LA_1LC0RE_0RA1LD_0LC0LF_0LB1RC_0LA---") c0.
Proof. solve_hlin_nonhalt 4. Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB0LE_1LC1RC_1LA0RD_0LB0RC_0LF1LD_---0LB") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB1LD_0RC1LE_0LD0RA_0LB---_0LF0LA_1LB0LA") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB1LC_0RC1LE_0LD0RA_0LB---_0LF0LA_1LB0LA") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB1RE_0LC0RD_1LD0LC_0RA1RF_1RD---_1LC1RF") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB0RF_0LC1RA_1LE0RD_0RB---_0LF0LC_1RA1RC") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB1LA_1LC0RA_0LF0LD_1LE1LA_1RB1LC_---0LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB1LA_1LC0RA_0LF0LD_1LE1LE_1RB1LC_---0LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB1LC_1LC0RE_0LF0LD_1LA1LA_1RB1LA_---0LA") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB1LE_1LC0RA_0LF0LD_1LE1LA_1RB1LC_---0LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LF_0LF0RD_1RA0LB") c0.
Proof. solve_hlin_nonhalt 5. Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB0LC_1RC0RA_0LD1LA_---1LE_0LF0LA_1RE0LA") c0.
Proof. solve_hlin_nonhalt 5. Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB0RF_0LC1LF_---1LD_0LE0LF_0LF0LF_1RA0LB") c0.
Proof. solve_hlin_nonhalt 5. Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB---_1RC1RF_1LD0RA_1RF0LE_1RA0LC_1LD0RD") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB1LF_1LC1RA_1LE0LD_1LC0RE_1RF1RD_---0RB") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB0RC_0LA0RE_1LD0LC_1LA1RA_0RF1RA_---1RB") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB1RE_0LC0RD_1LD0LC_0RA0RF_1RD---_1LB1LE") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB1LA_1RC1RB_1LD1RF_---0LE_1RA0LB_1RA0RC") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB1LA_1RC1RB_1LD1RF_---0LE_0RF0LB_1RA0RC") c0.
Proof. solve_hlin_nonhalt 2. Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB0RE_1LC1RD_1LA1LB_---1RA_1RC1LF_0LF1LC") c0.
Proof. solve_hlin_nonhalt 3. Time Qed.


