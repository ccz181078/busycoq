From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Ltac solve_hlin_nonhalt_T T :=
  apply (decide_hlin_nonhalt_spec _ default_config T);
  vm_cast_no_check (eq_refl true).

Ltac solve_hlin_nonhalt :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T 1000000%N)
  end.

Lemma nonhalt1: ~halts (TM_from_str "1RB0RC_0RC0RF_1LD1LE_0LC---_1LA0LA_0RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1RA_0RC0LF_0RD0RF_1LE0RA_1LB---_1RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1RF_1RC1RA_1LD0LE_1LB0LC_1LD0RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0LC_0RC1RE_0LD1RB_1LA1LC_0RF---_1LF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RC_0RC1RA_1LD1RB_0LE0LC_1RA1LF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB1RE_1LC0LE_1RA0LD_1LB1LD_---0RF_0LC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0RC_0RC0RF_0LD1LE_0LC---_1LA0LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0RC_1LC0LD_1RB0LB_1LE0RE_1RA0LF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1RF0RA_0LE0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB1LD_1RC0RA_1LB1RA_0LE0LF_---0LF_0RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0LC_1LA1RF_1LD0LE_0RE0RF_---1LA_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB0RC_1LC0LE_1RD0LB_---0RA_0LF0RF_1RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LE0LF_1RB0RA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE1LF_0LA0LC_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB1LC_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1LE_0RC---_1LD1RD_0LE1RA_0LA0RF_1RC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB0RD_0LC1RA_1LA1LB_1RE1LB_1LF0RD_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB1RF_1LC0RE_0LD1LC_1RA---_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB1RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB0RD_1LC1LB_---1LD_1RE1LF_0RA0RD_0LD0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1RF_0LC1RE_0RD0LB_1RA---_1LC0RC_0RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB1RF_1RC1LB_1LC0LD_---1LE_0RE1LF_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_1LA1RA_0LA1LC_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1RC0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1LA0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB1RA_1LC0LC_0LF1LD_1RE1LC_0LA0RA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0LE_0RC0RB_1LD1RF_0LA0LC_1LA---_0RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_1RB1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB0RC_1LC1RA_1RD0RD_1LF0LE_1LB1RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0LD0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1LF0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0RF_0LC0RA_1LE1LD_1LC---_1LA0LE_0RB0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0RC_1RC1RA_1RD1LC_1LD0LE_---1LF_0RF1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1RB1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB1LA_1RC0LE_0RD0LF_0RE0RC_1LE0LA_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB0RD_0RC0RE_1LD1RB_0LE---_1RA0LF_1LE1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB0RD_0LC0RC_0RD1RC_0LE1LF_1LD---_1LA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB1RC_0LC0RA_0RF1LD_1LE0LA_1RD1LB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE0LF_0LA0LC_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB0RE_1LC0RA_1LA0LD_1LA1RA_1RF0LB_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB1RC_0LC0RC_0RA1LD_1LC0LE_1LA1LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB1LD_1RC1RF_1LC0LD_1LB1RE_1RD0RB_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_---0LE_1RA1LF_1RA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_1RB1RA_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB0RD_1RC0RB_1LA1LF_0LA1LE_0LC---_1LD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD0LB_1LE0LD_1RC1RA_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB0RE_1LC1LB_1LD1RC_0RE0LB_1RC1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB0LD_0LC1RC_1LA1RD_0RC0LE_---0LF_1RA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB1RF_1LC0RE_---1LD_0LE1LC_0RA1LF_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_0RB1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB0RF_1LC0RA_1LE1LD_1LC---_1LA0LB_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RE_1LF0LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB1LE_1RC1LE_1LD0LD_1RF0RA_1LB0LC_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB0RC_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB1RF_1LC0LD_1RE1RD_---0LE_1RF0RF_1LB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB0LC_1LC0RE_1LF0LD_1LE---_1RB0RA_1LE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LF0RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB0LF_1RC0RE_0RD0RA_1LE1RC_0LA---_1LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_0LA0LF_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB0LF_0LC0RE_0LA1LD_1RB1LB_1RD0RD_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB0RF_1LC0RD_1LA1LC_0RF0RE_---1LA_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD0LA_1LA0RB_1LC1LE_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB0RC_0LC1LD_1RA1LB_1LB0RE_---1RF_0LA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA0LF_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LB1LD_---0RF_1LD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_0LA0LB_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB1RC_1LC1LD_1RA0LD_0LB1RE_1RF0RA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB1LE_1RC---_1RD0LF_0LA0RB_0LB1LF_0LC0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB0LB_0RC0LD_1LA1RE_1RB1LB_1RC1RF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD0RB_1LE---_1LF1LB_1LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RB1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1RB1LA_1RC1RD_0LA1RB_0LF0LE_1RF1LD_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1RB1RE_1LC1RA_1LA0LD_0RB0LF_---0LF_1RD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1RB1RA_1RC0RF_0LD0RA_1LB0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1RB0RF_1LC1LD_1LA1LC_0RF1RE_---0RD_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1RB1RA_1RC0LE_1RD1LC_0LB0RA_1RB0LF_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1RB0LD_1RC1RA_1LA0RE_0LC1LC_0RA0RF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1RB1RD_0RC1RA_1LD1RB_0LE0LC_1LA1LF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1RB0LD_1LC1RC_---1RA_1LF1RE_0RD0LC_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1RB1LC_0RC0RE_1LD0RE_0LA1LF_0RD0RA_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1RB0LD_1RC1RA_1LA0RE_0LC1LC_0RF0LC_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RA0LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1RB1RF_0LC1RD_1LE1LD_1LC0RB_1RF0LB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD1RC_---0RE_1RF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_---1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1RB0LD_0RC0RE_1RD---_1LA0LF_1RF0RD_1LD1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE0LD_1LE1LD_1LB0RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1RB1LB_0LC0RE_0LD0RC_1LA0LF_1RA0RA_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1RB1LB_1RC1RE_1LD1RB_---0LA_0RC0LF_1RE1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1RB1RA_0RC0LF_0RD1LE_1LE0RA_1LB---_1RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1RB0RC_1LC0LF_0LE0LD_1LC0LF_1RA---_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1RB0RF_1RC0RC_1LD0LE_1RA0LC_1LD0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1RB1LC_1LC0RD_---1LA_0RF1LE_1RF0LD_1RB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1RB0LC_1RC1RF_0LD1RE_1LA1LE_1LD0RC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1RB1RC_1LC0RA_0LF0LD_1LA1LE_1LA0LF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt98: ~halts (TM_from_str "1RB1RC_0LC0RC_0RA1LD_1LC0LE_1LA1LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt99: ~halts (TM_from_str "1RB1RF_1LC1LE_1RD0LB_---0RA_1LB0RA_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt100: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_1RD1RF_1RD1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt101: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD1LA_0RF0RE_---1LF_1LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt102: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE1LF_0LB0LE_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt103: ~halts (TM_from_str "1RB1RE_1LC0RD_1LD1LC_0RA---_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt104: ~halts (TM_from_str "1RB1LF_0RC0LA_1RD---_1LE0RE_1RC1LF_0LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt105: ~halts (TM_from_str "1RB0LC_0LC1RF_1LE1RD_0RC1RB_0LA1LA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt106: ~halts (TM_from_str "1RB0LD_1RC0RE_1LA0RF_1LA0LC_1RD0RA_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt107: ~halts (TM_from_str "1RB1RB_1RC1LE_1LD1LF_1RD0RB_1LB0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt108: ~halts (TM_from_str "1RB0LD_1RC1RF_0LA1LA_1LC1RE_0RD0RC_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt109: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RB0LB_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt110: ~halts (TM_from_str "1RB---_1LC0RF_1LD1LB_1RE0LF_1RA1RE_0LC1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt111: ~halts (TM_from_str "1RB0LB_0RC0RF_0LD0RF_1LE---_0LA1LC_0RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt112: ~halts (TM_from_str "1RB0LC_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt113: ~halts (TM_from_str "1RB1RC_0LA1LD_0RD0RC_1LE0RA_0LF---_1LB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt114: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_1RE0LE_---0LA_1RC1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt115: ~halts (TM_from_str "1RB1LC_1LA0RD_1LA1LF_0LA0RE_1LD1RD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt116: ~halts (TM_from_str "1RB0LD_1LC0RE_---0LD_1LA0LB_1RF0LB_1RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt117: ~halts (TM_from_str "1RB1RA_0RC---_1RD0LC_0RE0RD_1LF0RA_1LF1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt118: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_1LA0LE_0LA1LC_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt119: ~halts (TM_from_str "1RB0RA_0LC0LA_0LD1LB_1RE1LF_1RE1LA_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt120: ~halts (TM_from_str "1RB1LC_0RC0RC_1LD0RE_1LA0LC_1LC0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt121: ~halts (TM_from_str "1RB1RF_1RC0RD_1LD0LE_1RA0LC_1RC0LB_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt122: ~halts (TM_from_str "1RB1LA_1LC0RE_0LE1RD_0LA1RC_---0RF_1LF0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt123: ~halts (TM_from_str "1RB1RD_0LC0RF_1RE1LD_1LC1LB_---0RA_1LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt124: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD1RE_0LA1LA_0LE0RD_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt125: ~halts (TM_from_str "1RB0RD_1LC1RD_1RA0LD_1RA0LE_1RC0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt126: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0RC0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt127: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD0RF_0LE0RB_1LC0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt128: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LE0LB_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt129: ~halts (TM_from_str "1RB1RA_1LC0LF_0LD0LB_1RE---_0LA0RC_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt130: ~halts (TM_from_str "1RB1RD_1LC0RD_1LA1LB_0RA1LE_1LF0LC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt131: ~halts (TM_from_str "1RB0LA_1LC0RD_---1LA_1RE1RE_1RF0RB_1RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt132: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LB_1RB0LF_0RF---_0LC1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt133: ~halts (TM_from_str "1RB1RC_0LC0RC_0RA1LD_1LC0LE_1LA0LF_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt134: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA0LD_0LE1RF_0RB1LD_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt135: ~halts (TM_from_str "1RB0RC_1LC1RD_1RA0LD_1RA0LE_1RC0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt136: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt137: ~halts (TM_from_str "1RB1LD_1LC0RE_1LE1RA_---0LC_1RB0RF_1RD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt138: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt139: ~halts (TM_from_str "1RB0RF_1LC0RA_1LE1LD_1LC---_1LA1RB_1RB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt140: ~halts (TM_from_str "1RB1LE_1RC0RA_0LD1LD_1RF1LE_0LD0LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt141: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LE0LC_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt142: ~halts (TM_from_str "1RB0RF_1RC1LF_0LD1LC_1RF0LE_---1LB_0RA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt143: ~halts (TM_from_str "1RB---_1RC1RB_0LD1LC_1RF1LE_1LA0RC_0RF0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt144: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LC0LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt145: ~halts (TM_from_str "1RB1RC_1LC1LE_1LA0LD_0LC0LB_---1RF_0RA0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt146: ~halts (TM_from_str "1RB1LF_0RC---_1RD0RD_1RE1RD_0LA1LE_0LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt147: ~halts (TM_from_str "1RB1LA_1LC0RE_1RA0LD_1LA1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt148: ~halts (TM_from_str "1RB1LA_0LC0RE_1RE0LD_1RC1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt149: ~halts (TM_from_str "1RB1LD_1RC1LB_0LD0RF_0LF0LE_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt150: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD1RE_1RA0LC_0RC0RF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt151: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LE0LB_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt152: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD0RD_1LE---_1RF0LE_0LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt153: ~halts (TM_from_str "1RB0RC_1LC0RA_0RD1LD_0LE0RB_1LA0LF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt154: ~halts (TM_from_str "1RB0RB_1LC0LE_---0LD_1LA1RF_1LD1RF_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt155: ~halts (TM_from_str "1RB---_1RC1RF_1LD0LE_1RE0LC_0RF0RA_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt156: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RF1LC_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt157: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt158: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_1LE0LB_0LA0LC_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt159: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE0LD_1LB1LD_---1RF_1LD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt160: ~halts (TM_from_str "1RB1RF_1LC1RA_---0LD_0RE1LA_1RF1LF_0RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt161: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE1RF_1LE0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt162: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_1LC1LB_1LD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt163: ~halts (TM_from_str "1RB0LC_1LC1LE_0RD1LB_1RE1RD_1LF0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt164: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA0LE_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt165: ~halts (TM_from_str "1RB1RA_1LC---_1LE1LD_1LC0RF_1RA0LF_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt166: ~halts (TM_from_str "1RB0RC_1LC0LD_1RA0LB_0LE0RF_0RA1LD_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt167: ~halts (TM_from_str "1RB0RC_1LC1LE_1RD0LB_---0RA_1LF0RF_1LF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt168: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_0RE1LF_0LC1RD_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt169: ~halts (TM_from_str "1RB1LC_1RC0RD_1LD1RB_1RF1RE_---0LA_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt170: ~halts (TM_from_str "1RB0RB_1LC1LD_1LA1LC_0RF1RE_---0RD_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt171: ~halts (TM_from_str "1RB0LD_0RC1RF_1LD0RA_0LE1RB_1LA0LD_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt172: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE---_0RF0LC_1LB1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt173: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_0RE0RC_---1RF_0RA1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt174: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_1RF1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt175: ~halts (TM_from_str "1RB1RA_0LC---_1LE1LD_1LC0RF_1RA0LB_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt176: ~halts (TM_from_str "1RB0RF_1LC0RC_1RC1RD_1LA1RE_1LF1RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt177: ~halts (TM_from_str "1RB1RF_0RC0RB_1RD0LE_1RE0RA_1LC0LE_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt178: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_0LE1LD_1RB---_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt179: ~halts (TM_from_str "1RB0LF_0LC1RA_---0RD_1RE1RF_1LA1LF_0LE1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt180: ~halts (TM_from_str "1RB0LF_1LC1RD_0LE0RB_0RC1RA_1LA---_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt181: ~halts (TM_from_str "1RB0RD_0RC0RE_1LD1RB_0LE1RF_1RA0LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt182: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB0RC_0RA---_0LD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt183: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt184: ~halts (TM_from_str "1RB0RC_1LC0LF_0RD0LB_1RA1LE_0LD---_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt185: ~halts (TM_from_str "1RB1LF_1LC0RA_1LE1RD_---0RB_1LA0LB_0LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt186: ~halts (TM_from_str "1RB1LD_1LC1RF_1RD0LD_0RB0LE_---1LA_0RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt187: ~halts (TM_from_str "1RB1RF_1LC1RB_0RE0LD_1LB1LD_---0RA_1RB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt188: ~halts (TM_from_str "1RB1LD_1LC0RC_1RE0LD_0RB0LF_1LF1RA_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt189: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_1LA0LB_1LC0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt190: ~halts (TM_from_str "1RB1RF_1LC0RA_1RE1LD_0LC0LA_0RA---_0LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt191: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0LE0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt192: ~halts (TM_from_str "1RB1LC_0LC0RC_1LE0RD_0LE0RF_1LA1LD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt193: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1RB1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt194: ~halts (TM_from_str "1RB1LF_1LC0RD_0LD1RC_---0RE_1LF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt195: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---0RF_1RD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt196: ~halts (TM_from_str "1RB1LE_0RC1LF_1RD1RF_1LE0RB_---1LA_1RC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt197: ~halts (TM_from_str "1RB0RF_1LC0LE_0LD0LB_1RA---_1LB0RD_0LD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt198: ~halts (TM_from_str "1RB0RE_1LB0LC_1LA1RD_1RC0RA_---0LF_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt199: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB1RF_1LB0RC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt200: ~halts (TM_from_str "1RB1LD_1RC1LB_0LD0RF_1LB0LE_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt201: ~halts (TM_from_str "1RB0RF_1RC1RE_1LD1RF_1LA0LD_0RC---_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt202: ~halts (TM_from_str "1RB0LE_1RC0LC_1LD1LE_---0LA_0LB1RF_1RB0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt203: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB0RF_1LB0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt204: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LB1LD_---0RF_0LC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt205: ~halts (TM_from_str "1RB0RF_1LC1RC_0RE0LD_1LB0LB_0RA1RB_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt206: ~halts (TM_from_str "1RB1LB_0LC1LF_1RD1LC_1LF0RE_1RC1RE_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt207: ~halts (TM_from_str "1RB0LD_1RC1RF_0LA1LA_1LC1RE_0RD1RB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt208: ~halts (TM_from_str "1RB1RE_1LC1LE_1RD0LD_0LB1RC_0LB1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt209: ~halts (TM_from_str "1RB1RE_1LC0RF_1LD1LC_0RA---_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt210: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_1LC1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt211: ~halts (TM_from_str "1RB---_1LC0RA_1LE0LD_1LE0RE_1RD0RF_1RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt212: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_0LE0LB_1LC0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt213: ~halts (TM_from_str "1RB0LB_1LC0RF_1LE0LD_1LE0RE_1RD0RA_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt214: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RF1RD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt215: ~halts (TM_from_str "1RB1RB_1LC1LF_1RD0LB_---1RE_0RA1RC_1LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt216: ~halts (TM_from_str "1RB0RF_0RC1RE_1LD0LE_0LE1LE_1RA0LD_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt217: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LB1LD_---0RF_1RD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt218: ~halts (TM_from_str "1RB0LB_1RC0RE_1LD0RF_---1LA_1RB1LF_0LE0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt219: ~halts (TM_from_str "1RB0RE_1LC0LF_1RA0LD_1RC0LB_1RA---_1LC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt220: ~halts (TM_from_str "1RB0LE_0LC0LF_1LA0RD_1RC1RB_1LD0LF_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt221: ~halts (TM_from_str "1RB0LD_1RC1LB_1LA0RF_---1LE_1LF1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt222: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_1RD1RF_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt223: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA0RF_1LA0RD_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt224: ~halts (TM_from_str "1RB0RD_1RC0RC_1LD0LF_0RE0LD_0LC1RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt225: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LB_1LA1RD_1LB1RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt226: ~halts (TM_from_str "1RB0LE_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt227: ~halts (TM_from_str "1RB0LF_0LC0RC_1RA1LD_0LE1LF_0RB---_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt228: ~halts (TM_from_str "1RB0RD_0RC---_0RD1LE_1LB1RC_1LC0LF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt229: ~halts (TM_from_str "1RB1LC_1LC0RA_0LE0LD_0LE1LE_1RF1LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt230: ~halts (TM_from_str "1RB1LA_0LC1LB_1RD0LC_0RE---_0RF0RC_1LF0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt231: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA1RF_1LA1LD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt232: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA1LF_1RB0LC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt233: ~halts (TM_from_str "1RB1RE_1LC0LC_1RD1LC_---0RE_1LF1RA_0LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt234: ~halts (TM_from_str "1RB0LD_1RC1RF_0RD0RA_1LE1RC_0LA0LD_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt235: ~halts (TM_from_str "1RB1RF_1LC1RB_1RA0LD_0LE1LD_0RC1RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt236: ~halts (TM_from_str "1RB0LE_1RC1LF_1RD0RA_0RE0RF_1LA1RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt237: ~halts (TM_from_str "1RB0RE_1LC0RF_---1LD_0LE0LA_1RA1LF_0RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt238: ~halts (TM_from_str "1RB0LD_0LC1RA_1RE1RD_0LE1RF_1LA1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt239: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0RB0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt240: ~halts (TM_from_str "1RB0LF_1LC0RF_1LE1LD_1LB---_1RB0RA_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt241: ~halts (TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt242: ~halts (TM_from_str "1RB---_1LC1LF_1RE0LD_0LB1RF_1RA1RE_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt243: ~halts (TM_from_str "1RB1RC_1LC0RA_1LF0LD_1LA1LE_1LA0LB_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt244: ~halts (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_0RE1RA_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt245: ~halts (TM_from_str "1RB0LB_1LA0LC_1LD0RD_1RE0LF_1RB0RA_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt246: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt247: ~halts (TM_from_str "1RB0RA_0RC1LE_1RD1RC_1LE0RF_---1LF_0LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt248: ~halts (TM_from_str "1RB1LD_1LC1LE_0LA0LD_1LE---_1RF1LB_0RC0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt249: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---1RF_0RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt250: ~halts (TM_from_str "1RB1RD_1RC1RA_1LD0LE_0LF0LC_1LD0RA_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt251: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB0RF_1LB0RC_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt252: ~halts (TM_from_str "1RB1LF_1LC0RD_0LD1RC_---0RE_1RF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt253: ~halts (TM_from_str "1RB1RF_1LC0RE_1LD1LC_0RE---_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt254: ~halts (TM_from_str "1RB1LE_1LC0LA_---1RD_1RE1LD_0LB0RF_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt255: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RF_1LE---_1LF0LC_1RC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt256: ~halts (TM_from_str "1RB0RD_1LC0LF_1LD0LB_1RA1RE_1RF---_1LC0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt257: ~halts (TM_from_str "1RB1RF_1LC0RA_0RE1LD_0LC0LA_1LA---_0LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt258: ~halts (TM_from_str "1RB1RC_1LC0RA_0LF0LD_1LA1LE_1LA0LB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt259: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_0RE1RF_1RD0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt260: ~halts (TM_from_str "1RB1RE_1LC0LD_1RD0LB_0LF0RE_1RA0LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt261: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_0LA1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt262: ~halts (TM_from_str "1RB1LB_1LC1LE_1RA0LD_1LE1LF_0LC0RE_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt263: ~halts (TM_from_str "1RB1RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt264: ~halts (TM_from_str "1RB0RE_1RC0LF_1LD---_0LE0LD_1LF0RF_1RA0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt265: ~halts (TM_from_str "1RB0LC_0RC0RB_1RD0LE_1LA0RE_1LF0RE_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt266: ~halts (TM_from_str "1RB1RE_1LC0RE_0LD1LB_1LA1LE_0RA0LF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt267: ~halts (TM_from_str "1RB0RB_1LC0LF_---0LD_1LE1LD_0RF1RB_1RE1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt268: ~halts (TM_from_str "1RB0RE_1LC---_1RA0LD_1LC0LF_1RF0RD_1LD1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt269: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LB1LD_---0RF_1LA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt270: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_1LC0RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt271: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_0RE0LB_---1LA_1RC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt272: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LE0LC_1LA0LC_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt273: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt274: ~halts (TM_from_str "1RB0LE_0RC---_1RD0RF_1LA0RC_1LF0LC_1RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt275: ~halts (TM_from_str "1RB0LD_0LC0RE_---1RD_1LA0LB_1RF0LB_1RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt276: ~halts (TM_from_str "1RB1RA_0LC0RA_1LE0LD_1RC1LB_---1RF_1RB1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt277: ~halts (TM_from_str "1RB0RD_1LC1RD_0LB0LD_1RA0LE_1RC0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt278: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_0RC0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt279: ~halts (TM_from_str "1RB1LA_1LA0RC_0RD1RC_1LE0LF_0LD---_1RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt280: ~halts (TM_from_str "1RB0LE_0RC1RB_1RD---_1LA1LF_0LD1RF_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt281: ~halts (TM_from_str "1RB0RC_1LC1LE_1RE0LD_1RA0LF_1LB0RA_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt282: ~halts (TM_from_str "1RB1RF_1RC1LB_0LC0LD_---1LE_1RA1LF_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt283: ~halts (TM_from_str "1RB1RD_1RC1RA_1LD0LE_1LF0LC_1LD0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt284: ~halts (TM_from_str "1RB0RF_0RC0RB_1RD0LE_1RE0RA_1LC0LE_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt285: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA1LB_---1RE_1LF0RF_1RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt286: ~halts (TM_from_str "1RB1RE_1RC---_1LD1LF_0RA1LD_0RA1RF_1RE0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt287: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1LB1RF_0LF0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt288: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_1LA1LC_0LA1LC_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt289: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE1LF_0LA0RF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt290: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_---1LE_0RE1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt291: ~halts (TM_from_str "1RB1RE_1LC1RC_0LD0RB_1RF1LE_1LD1LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt292: ~halts (TM_from_str "1RB---_0LC1LF_1RD1LB_0RE0RC_1RA0RC_1LB1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt293: ~halts (TM_from_str "1RB0LF_1LC1RE_1LA0RD_0RC0LC_0RB1RD_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt294: ~halts (TM_from_str "1RB1LC_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt295: ~halts (TM_from_str "1RB1RF_1LC0LD_1LA0LC_0RB1RE_0RA---_1RD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt296: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_1RF0LC_1LD0RA_0RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt297: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1RD0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt298: ~halts (TM_from_str "1RB1RF_0LC1RE_1RC0RD_1LB1LA_0RC1RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt299: ~halts (TM_from_str "1RB0LD_1RC0RF_1LD---_1LE1LD_1LF0LB_1RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt300: ~halts (TM_from_str "1RB0RF_1RC0RA_1LD---_1LE1LD_1LA0LB_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt301: ~halts (TM_from_str "1RB1LD_1LC1RE_1RE0LD_0RB0LF_0RB1RA_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt302: ~halts (TM_from_str "1RB0RF_0LC0RA_0RD1RC_1LE---_1LA0LB_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt303: ~halts (TM_from_str "1RB0LE_0RC0RD_1LD0LA_1LA1RF_1LC1LE_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt304: ~halts (TM_from_str "1RB1RF_1LB0LC_1RC1LD_1LB0RE_---1RA_1RA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt305: ~halts (TM_from_str "1RB1LA_1RC0RD_0LD1RF_---0RE_1LE0LA_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt306: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA0LF_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt307: ~halts (TM_from_str "1RB0RE_0LC0LF_1RD1LB_0RA0LE_1RA---_0LD0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt308: ~halts (TM_from_str "1RB1RD_1LC0RE_1LA1RA_0RB0LD_1RD1RF_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt309: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LB_1RA1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt310: ~halts (TM_from_str "1RB0RC_1LC1RA_0RD1RD_1LF0LE_1RA1LB_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt311: ~halts (TM_from_str "1RB0LD_1RC1RA_1LA0RE_0LC1LC_0RA0RF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt312: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD---_1LE0RF_1LA1LD_0LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt313: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF0RD_---0LE_1LB0LB_1LE1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt314: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1LB0RA_1RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt315: ~halts (TM_from_str "1RB1RE_1LC1LE_0RD1LB_1LC1RD_1LF0RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt316: ~halts (TM_from_str "1RB0RE_0RC0RF_1LD---_1LA0LB_1RF0LC_1RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt317: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_0RE1RE_1LF0LC_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt318: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LA_0LA1RA_0RD0RF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt319: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1RB0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt320: ~halts (TM_from_str "1RB0RF_0RC0RE_1LD1RB_0LE0LC_1RA0LC_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt321: ~halts (TM_from_str "1RB0RD_1LC---_0LD1LB_1RE1LF_0RA0RD_0LD1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt322: ~halts (TM_from_str "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---1RF_1LD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt323: ~halts (TM_from_str "1RB0LE_1RC0RD_1RD---_1RE0RA_1LA0LF_1LA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt324: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_1LC0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt325: ~halts (TM_from_str "1RB---_1RC1RF_1LD0LE_1RE0LC_1LD0RA_1LF1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt326: ~halts (TM_from_str "1RB0LE_0RC1RF_1LD1RA_0LA0LE_0RA0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt327: ~halts (TM_from_str "1RB0RB_1RC1LC_0LD0RA_0LE0RD_1LB0LF_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt328: ~halts (TM_from_str "1RB0LE_0RC0RD_1RD---_1RE0RA_1LA0LF_1LA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt329: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_1LE1LD_0RB---_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt330: ~halts (TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE---_1LA1LF_1RF1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt331: ~halts (TM_from_str "1RB0LC_0RC1RA_1LD1RB_0LE0LC_1RA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt332: ~halts (TM_from_str "1RB0RE_1RC0RA_1LD---_1LF1LA_1RA0LD_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt333: ~halts (TM_from_str "1RB0LD_1RC1LE_1LA0RB_0LF1RA_0LB1RC_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt334: ~halts (TM_from_str "1RB0RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt335: ~halts (TM_from_str "1RB1RE_1LC0LE_1RA0LD_1LB1LD_---1RF_1RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt336: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD1RC_---0RE_1LF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt337: ~halts (TM_from_str "1RB0RE_1RC0RA_1LD1LC_1LE1RD_---0LF_1LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt338: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LE0LF_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt339: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LE0LB_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt340: ~halts (TM_from_str "1RB1RE_1LC0LC_1RD1LC_---0RE_1LF1RA_0LB0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt341: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD1RE_0LA1LA_0RC0LF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt342: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0RF0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt343: ~halts (TM_from_str "1RB1LE_0RC0RD_1LD0RD_1RC1RA_---1LF_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt344: ~halts (TM_from_str "1RB1LD_1RC1LB_1LA0RF_---0LE_1LF1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt345: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LB0LE_---1LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt346: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0RD0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt347: ~halts (TM_from_str "1RB0LC_0LC1RF_1LE1RD_0RC0RE_0LA1LA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt348: ~halts (TM_from_str "1RB0RC_1LC0RA_0RF0LD_1LE1RF_1LA1LD_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt349: ~halts (TM_from_str "1RB0LE_0RC0RD_1LA0RF_1RE0RA_1LA0LC_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt350: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt351: ~halts (TM_from_str "1RB0RC_1LC0LF_1RD0LB_1RA1RE_1RD---_1RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt352: ~halts (TM_from_str "1RB0RF_0RC0LE_1LC0LD_1RA1LD_0RB1LB_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt353: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0RF_1LE1LE_0LA0LB_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt354: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_1LE0RB_1LB0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt355: ~halts (TM_from_str "1RB0LE_1RC1LB_1LB0RD_1RE1RD_1LF0LB_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt356: ~halts (TM_from_str "1RB1RD_1LC0RA_0LE0LD_0LE1LE_1RF1LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt357: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_1RB0LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt358: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA---_0RE1RD_1LF0LA_0LF0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt359: ~halts (TM_from_str "1RB1LB_1LC1LF_1RD1LC_1LA0RE_1RC1RE_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt360: ~halts (TM_from_str "1RB0RC_1LC0LD_1RA0LB_0LE1RF_0RA1LD_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt361: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA1LF_1RA1RE_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt362: ~halts (TM_from_str "1RB1RD_1LC0RD_---0LD_1LE0LF_1RF1LD_0LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt363: ~halts (TM_from_str "1RB1LC_0RC1RF_1RD1LF_0LE0RA_---1LB_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt364: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1LA1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt365: ~halts (TM_from_str "1RB0LB_1LA1LC_1LA1RD_0RF1RE_0LC1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt366: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD0RA_0RD1LE_1LF---_0LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt367: ~halts (TM_from_str "1RB0RE_0RC---_1RD1LF_0LA1LA_1LB1RC_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt368: ~halts (TM_from_str "1RB1RA_1LC1LE_1RE1LD_0LB0LF_---0RA_0RD1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt369: ~halts (TM_from_str "1RB1LC_1LA0RD_1LA0LF_0LA0RE_1LD1RD_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt370: ~halts (TM_from_str "1RB0LB_0LC1RA_1LA1LD_0LC1RE_---0RF_1RC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt371: ~halts (TM_from_str "1RB1RA_1LC---_0LE1RD_1LE0RC_1LF1LD_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt372: ~halts (TM_from_str "1RB---_1LC0RF_1RE1LD_0LE1LB_0RA0LC_1RA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt373: ~halts (TM_from_str "1RB0LE_1RC1RA_1RD0RB_1LE---_1LF1LA_1RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt374: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA0RF_1LA0RD_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt375: ~halts (TM_from_str "1RB1LE_0LC0RF_---1LD_0RA1RE_1LA0LB_1RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt376: ~halts (TM_from_str "1RB0LC_1LA1LC_1LA1RD_0LB1RE_0RF1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt377: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_0LB0LB_1RC---_0RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt378: ~halts (TM_from_str "1RB1RA_1RC0RD_1LD0RA_---1LE_1LB0LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt379: ~halts (TM_from_str "1RB0RE_1LC1RA_1RA0LD_0RB0LF_---1LF_1RD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt380: ~halts (TM_from_str "1RB0LE_0LB1RC_1RD---_0RE0RA_1LF1RD_0LA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt381: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE0LD_1LB1LD_---1RF_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt382: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LE0LC_1RA0LC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt383: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_1RC0RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt384: ~halts (TM_from_str "1RB1RD_1LC1LE_1RE1LD_1RB1LF_---0RA_1LD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt385: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA0RF_1LA1RB_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt386: ~halts (TM_from_str "1RB0RE_1RC1RA_1LD0LD_0RB1LC_1RB0RF_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt387: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1LC1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt388: ~halts (TM_from_str "1RB---_1LC0RC_1RF1RD_0RB1LE_1LB0LE_1RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt389: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0RF_0LD1RA_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt390: ~halts (TM_from_str "1RB0RD_0LC0RA_1RE1LD_1LC0LF_1LA0LB_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt391: ~halts (TM_from_str "1RB0LB_0RC0RC_1RD0RE_1LE1RC_---0LF_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt392: ~halts (TM_from_str "1RB1RF_0RC0LB_1LD0RA_1LE1RE_1RC1RB_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt393: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA0LB_1RD0RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt394: ~halts (TM_from_str "1RB0RC_1LC0LF_0LE0LD_1LC0LF_1RA---_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt395: ~halts (TM_from_str "1RB1LB_1RC1LA_1RD0RE_1LB0RF_---0LB_1LE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt396: ~halts (TM_from_str "1RB1RA_1RC0LE_1RD1LC_0LB0RA_0LA0LF_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt397: ~halts (TM_from_str "1RB0RE_1LC0RA_1RD1LC_1LE1RD_---0LF_1LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt398: ~halts (TM_from_str "1RB1RA_1LC0LF_---0LD_1RE0LE_0LB1LD_1RF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt399: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA1LF_1RA1RE_0LE1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt400: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE0LF_0LA1LD_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt401: ~halts (TM_from_str "1RB1LB_1LA1RC_---0RD_1LA0LE_1LD1RF_0RE1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt402: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1LB0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt403: ~halts (TM_from_str "1RB1LC_0RC1RF_1RD1LF_0LE0RA_---1LF_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt404: ~halts (TM_from_str "1RB1LD_1LC0LF_1RA0LB_0RD1RE_---0RA_1LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt405: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LA_0LA1RA_0RD0RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt406: ~halts (TM_from_str "1RB0RB_1LC1RE_---0LD_1RE0LF_1RB0RA_1LE1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt407: ~halts (TM_from_str "1RB0RE_1LC1LB_1LD1RC_1RA0LB_1RB1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt408: ~halts (TM_from_str "1RB0RF_1RC0LD_0LD0RE_1LA1LB_0RA---_0RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt409: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE0LD_1LB1LD_---0RF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt410: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_1RC0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt411: ~halts (TM_from_str "1RB1RC_1LB0RA_1LD1RA_---0LE_1LF0LC_0LA0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt412: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1LF0RD_1LC0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt413: ~halts (TM_from_str "1RB---_0LC1RA_1LD0LD_0RB0RE_1RF1LB_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt414: ~halts (TM_from_str "1RB0LC_1RC0RB_1LD0RB_1LE0LD_1LA0LF_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt415: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_1LD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt416: ~halts (TM_from_str "1RB0RF_1RC1LD_1LD0RA_0LB1LE_1LB1RA_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt417: ~halts (TM_from_str "1RB1LE_0LC1LC_1RF0RD_1LE1RA_1LA0LB_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt418: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA1RF_1LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt419: ~halts (TM_from_str "1RB1LA_0LC0RF_1RA0LD_1RC1LE_---1LC_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt420: ~halts (TM_from_str "1RB1RE_1LC0LD_1RD0LB_1LF0RE_1RA0LD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt421: ~halts (TM_from_str "1RB1RD_0LC0RF_1RE1LD_1LC0LE_---0RA_1LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt422: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LB1LE_1LF0LD_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt423: ~halts (TM_from_str "1RB0LD_1RC1RF_1RD0RA_1LA0LE_1RD0LC_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt424: ~halts (TM_from_str "1RB1RD_1RC1RA_1LD0LE_1RF0LC_1LD0RA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt425: ~halts (TM_from_str "1RB1RC_0RC0LE_1LD1RB_1RA0LB_---0LF_1RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt426: ~halts (TM_from_str "1RB0RF_0LC0RE_1LA0LD_1RE1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt427: ~halts (TM_from_str "1RB1LC_0RC0RE_1LD0RE_0LA1LF_0LC0RA_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt428: ~halts (TM_from_str "1RB1LB_1RC1LE_1RD1LC_1LB0RF_---0LA_1RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt429: ~halts (TM_from_str "1RB1LD_1LC0LF_1RF0RD_1LA0LE_1LB---_0LA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt430: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LE0LF_1RB0RA_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt431: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LB0LE_---1LF_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt432: ~halts (TM_from_str "1RB1RD_1LC1LF_1RF0RD_1RB1LE_1LD0LB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt433: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD0RA_0LE1LF_1RB1LC_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt434: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_---1LE_1RB1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt435: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_0LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt436: ~halts (TM_from_str "1RB0RD_1LC1RD_---0LD_1RA0LE_1RF0LF_0LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt437: ~halts (TM_from_str "1RB0LD_1RC1RA_1RD1RE_1LE1LA_0RC1LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt438: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB0RC_0RA---_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt439: ~halts (TM_from_str "1RB1LC_1LC0RA_0LD0LC_1RE0LE_0RB0LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt440: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1RE0LB_1RF1LE_1RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt441: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1RA1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt442: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_0LE0LB_---1RA_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt443: ~halts (TM_from_str "1RB0RC_1RC1RA_1RD1LC_1LD0LE_---1LF_1RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt444: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_0LB0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt445: ~halts (TM_from_str "1RB---_0RC1RF_1LD0RA_1LE0RF_1RE0LC_0RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt446: ~halts (TM_from_str "1RB1LE_1LC0LA_---1LD_1RE0RB_0LB0RF_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt447: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA0LF_1RB0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt448: ~halts (TM_from_str "1RB1LC_0LC1RF_1LD0RB_1RE0LA_---0RF_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt449: ~halts (TM_from_str "1RB0LF_1RC0RA_1LD0RA_---0LE_1LA1LE_1RB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt450: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_1RA1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt451: ~halts (TM_from_str "1RB0LD_1RC1RE_1LD0RF_1LE1LD_1RB0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt452: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RB0LE_---1LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt453: ~halts (TM_from_str "1RB1LD_0RC0RF_1LD0RF_1LE1LF_0LA1LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt454: ~halts (TM_from_str "1RB1LA_1RC0RD_0LD1RF_---0RE_1LE0LA_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt455: ~halts (TM_from_str "1RB0RC_1LC0LF_0LD0RD_1RA1LE_0LB---_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt456: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1LE0LB_1RF1LE_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt457: ~halts (TM_from_str "1RB0LB_1LC1LB_0RE1RD_1LA1RC_1LA1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt458: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_1RE0LB_---0LA_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt459: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_1LE1LD_1LB---_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt460: ~halts (TM_from_str "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---1RF_0RF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt461: ~halts (TM_from_str "1RB1LA_0LC0RE_0LE0LD_1RC1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt462: ~halts (TM_from_str "1RB0RB_0RC1RF_1LD0LE_0LE1LE_1RA0LD_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt463: ~halts (TM_from_str "1RB1RD_0RC0LF_1LD0RF_0LE1LC_1RA0LD_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt464: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---1LE_1LB0LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt465: ~halts (TM_from_str "1RB1RA_0RC1LB_1LD0LD_1RE1LC_0RA1RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt466: ~halts (TM_from_str "1RB0LD_1RC1RA_1LA0RE_1LB0LC_1LD0RF_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt467: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt468: ~halts (TM_from_str "1RB1RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt469: ~halts (TM_from_str "1RB0LF_1LC1RA_1RE1LD_0LB1LC_---0RC_1LD1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt470: ~halts (TM_from_str "1RB1RC_1LC0LD_1RD1LB_1LF1LE_---0RA_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt471: ~halts (TM_from_str "1RB0LF_1LC0RA_0RF0LD_0LE---_1RC1LD_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt472: ~halts (TM_from_str "1RB0RC_0LC1RA_0LD1LC_1LE0LF_1LA0RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt473: ~halts (TM_from_str "1RB1LA_0LC0RE_1RA0LD_1RE1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt474: ~halts (TM_from_str "1RB0LF_1RC---_1RD1RA_1RE0RC_1LA0RD_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt475: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LA0LB_0LB0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt476: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB0RC_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt477: ~halts (TM_from_str "1RB0LC_0RC1RB_1LD0RA_0LE---_1LB1LF_1LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt478: ~halts (TM_from_str "1RB0RC_0RC0RF_0LD1LE_1LC---_1LA0LA_0RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt479: ~halts (TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_1RF---_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt480: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_---1LF_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt481: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---1LE_0LA0LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt482: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt483: ~halts (TM_from_str "1RB1RD_1LC0RD_1LA1LB_0RA1LE_0LF0LC_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt484: ~halts (TM_from_str "1RB0RF_0RC0RA_1LD---_1LE0LB_1RB0RF_1RE0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt485: ~halts (TM_from_str "1RB0LE_1LC0RF_---1LD_1LE1LB_1LA0LD_1RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt486: ~halts (TM_from_str "1RB1RF_1LC0RD_1LA0LB_1RF0RE_0RC---_0RB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt487: ~halts (TM_from_str "1RB0RC_1LC1LE_1RD0LB_---0RA_1LF0RF_1RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt488: ~halts (TM_from_str "1RB1RF_1LC0LD_1RD0LB_1LC0RE_1RA---_1LF1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt489: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0LC_------") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt490: ~halts (TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_0LC1LC_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt491: ~halts (TM_from_str "1RB1RF_1LC0RE_---1LD_0LE1LD_0RA1LF_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt492: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE1RF_1LE0LB_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt493: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt494: ~halts (TM_from_str "1RB1RE_0RC0RA_0LD0RD_1LE---_0LB0LF_1LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt495: ~halts (TM_from_str "1RB0RF_1LC0RD_0LE1LA_1RC1RD_---1LF_1LC0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt496: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---0RF_1LD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt497: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_1RD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt498: ~halts (TM_from_str "1RB0LB_0RC1LF_1LD0RE_0LA1LC_1RC0RD_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt499: ~halts (TM_from_str "1RB0LD_0LC0RE_---1RD_1LA0LB_1RF1LC_1RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt500: ~halts (TM_from_str "1RB0RC_1LC1LE_1RD0LB_---0RA_1LF0RF_0RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt501: ~halts (TM_from_str "1RB1RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt502: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RA0LB_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt503: ~halts (TM_from_str "1RB0LD_1RC0LA_1RD1RF_1LB0LE_1LB0RA_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt504: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1LC0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt505: ~halts (TM_from_str "1RB0RE_1LC1RB_1RA0LD_1LB1LD_---1RF_1LD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt506: ~halts (TM_from_str "1RB1LD_1RC0LA_0RD1RF_1LE0RE_0LB0LA_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt507: ~halts (TM_from_str "1RB1RE_1LC1LD_1RA0LD_0LB1RF_1RA1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt508: ~halts (TM_from_str "1RB1RE_1RC0RF_1LD---_0LE1LD_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt509: ~halts (TM_from_str "1RB0LC_1LA1RC_1RD0LE_1RB1RE_0RA0LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt510: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE0LC_1RA0LC_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt511: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_0RE1RF_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt512: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt513: ~halts (TM_from_str "1RB0LF_0LC0RD_1LE1RD_0RC1LB_0LA0RD_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt514: ~halts (TM_from_str "1RB1LE_0RC---_1LD1RD_0LE1RA_0LA0RF_1RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt515: ~halts (TM_from_str "1RB1LF_0LC0LA_1RD1RC_1RE1LD_0LB0RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt516: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD0RA_1RB0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt517: ~halts (TM_from_str "1RB---_1LC0RC_1LE0LD_1LC0LB_1RF1RA_1RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt518: ~halts (TM_from_str "1RB1RB_1RC0RE_1RD0RA_1RE0LD_1LF0RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt519: ~halts (TM_from_str "1RB---_1LC0LF_0LD0LB_1RE---_1RB0RC_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt520: ~halts (TM_from_str "1RB1LE_0RC1LF_1LD0RA_1LE1LF_0LA1LD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt521: ~halts (TM_from_str "1RB---_1RC0LF_0LD0RC_0RA1LE_0LA1LF_0LB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt522: ~halts (TM_from_str "1RB1RE_1LB0LC_1RD1LC_1RA0RF_1RB0RB_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt523: ~halts (TM_from_str "1RB0RB_1LC0LF_---0LD_1LE1LD_0RF0LF_1RE1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt524: ~halts (TM_from_str "1RB0RC_0LC1LE_0RD1LB_1RA1RC_0LF---_1RF0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt525: ~halts (TM_from_str "1RB0LC_0LC1RF_0LE1RD_1LE0RC_1LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt526: ~halts (TM_from_str "1RB0LB_1LC0RE_0RB1LD_1LA1RE_0LA0RF_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt527: ~halts (TM_from_str "1RB0RD_0LC0RE_---0LD_1LA1LF_1RA1RE_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt528: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_1LE0RB_1RA1LA_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt529: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1LE0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt530: ~halts (TM_from_str "1RB1RE_1LC1RD_---0LD_1RA0LE_0RA0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt531: ~halts (TM_from_str "1RB1LD_0RC---_1LD0RE_0LA0LF_1RC1LD_0LE1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt532: ~halts (TM_from_str "1RB1LE_1RC---_1RD0RB_1LE0LA_0LF0LA_0RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt533: ~halts (TM_from_str "1RB0RE_0RC1RE_1LB1LD_0LE0LD_1RF0LC_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt534: ~halts (TM_from_str "1RB0RF_1LC0RD_1LA1LC_0RF1RE_---0RD_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt535: ~halts (TM_from_str "1RB0RF_1LC0LD_1RD0LB_0LE1RE_0RA0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt536: ~halts (TM_from_str "1RB1RD_0RC1RA_1LD1RB_0LE0LC_1LA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt537: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB1RF_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt538: ~halts (TM_from_str "1RB0RC_1LC---_1RA0RD_1RA0LE_1LF1LA_1LC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt539: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1LA1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt540: ~halts (TM_from_str "1RB0LC_0LA1RE_0RD0LF_1LA0RA_1RD1LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt541: ~halts (TM_from_str "1RB1RC_1LC0RC_0RA1LD_1LB0LE_1LA1LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt542: ~halts (TM_from_str "1RB1LD_1RC0LA_0RD1RF_1LE0RE_0LB0LA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt543: ~halts (TM_from_str "1RB0LC_1LA1RC_1RD0LE_1RB0RC_1RC0LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt544: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1RA0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt545: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1LC1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt546: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE1RF_1RA0LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt547: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1RB0LD_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt548: ~halts (TM_from_str "1RB0LE_1LC0LD_0LE1LD_0LB0RF_1RF---_0RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt549: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD1RF_1LD0LA_---0RD_1RD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt550: ~halts (TM_from_str "1RB0LC_0RC0RE_1LD1LA_0LA1RA_0RD1RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt551: ~halts (TM_from_str "1RB0LC_0RC1RA_1LD1RB_0LE0LC_1RA1LF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt552: ~halts (TM_from_str "1RB1RC_1LC1RD_0RA0LD_1RA0LE_0LA0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt553: ~halts (TM_from_str "1RB---_1RC0RF_0RD0RB_1LE---_1LB0LC_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt554: ~halts (TM_from_str "1RB1LD_1LC0RC_0LD0LD_1RE0LF_1RA0RA_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt555: ~halts (TM_from_str "1RB0RA_1LC0LF_1LE1LD_0LE---_1RA1LF_0LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt556: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE1LF_0LA1LD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt557: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_1LE0RB_1LC0LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt558: ~halts (TM_from_str "1RB1LC_1RC0RA_0LD1LD_1RF1LE_0RA0LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt559: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB1RE_0RF0RC_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt560: ~halts (TM_from_str "1RB0RB_1RC1LE_1LD0LF_1RA1LB_1LB0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt561: ~halts (TM_from_str "1RB---_1LC0RA_0LF0LD_0LE1RF_1RF1LD_0RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt562: ~halts (TM_from_str "1RB---_1LC0RB_0RE0RD_0LF0LE_1LD1RC_1RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt563: ~halts (TM_from_str "1RB1LA_1LA0RC_1RD1RC_1LE0LA_---1LF_1LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt564: ~halts (TM_from_str "1RB---_1RC1LE_1LD0LF_1RD0RB_1LB0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt565: ~halts (TM_from_str "1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LF_0RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt566: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt567: ~halts (TM_from_str "1RB1LA_1RC0RF_0LD1LD_1RF1LE_---0LC_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt568: ~halts (TM_from_str "1RB1LE_0LC1RD_1RB1LC_1RB1RE_1RF0LA_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt569: ~halts (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1RE0LE_---0RF_0RC1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt570: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0LB0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt571: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1RB1LD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt572: ~halts (TM_from_str "1RB1RE_0RC1RC_1RD0LF_0LA1LE_1LF0RB_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt573: ~halts (TM_from_str "1RB0RE_1LC1RA_1LA0LD_1LB0RF_0RD0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt574: ~halts (TM_from_str "1RB0RB_1LC0LE_0LE0LD_1LB1LD_1RF1RA_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt575: ~halts (TM_from_str "1RB---_0LC0LF_1RE1RD_1RC0LE_1LF0RA_1LD1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt576: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt577: ~halts (TM_from_str "1RB0RC_1LC1LE_1RF0RD_1RF0LE_1LF---_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt578: ~halts (TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE---_1RC1RF_1LF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt579: ~halts (TM_from_str "1RB1LC_1RC0RE_0LA1LD_1LA1RE_---0RF_1LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt580: ~halts (TM_from_str "1RB0RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt581: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB1LE_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt582: ~halts (TM_from_str "1RB0RF_0LC0RA_1LE1LD_1LC---_1LA0LE_0RB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt583: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA0LF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt584: ~halts (TM_from_str "1RB0RA_1LC0LD_1RA0LB_0LE0RC_0RF0LF_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt585: ~halts (TM_from_str "1RB0RC_1LC1RA_0RD1RD_1LF0LE_1RF1LB_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt586: ~halts (TM_from_str "1RB1LA_0LC1RE_1RF0LD_1LA1LC_0RA1RC_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt587: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD0RA_1LE1LA_---1LA_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt588: ~halts (TM_from_str "1RB0LC_1LC---_1RE0LD_0LC1LC_1RF0RF_0RA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt589: ~halts (TM_from_str "1RB---_1LC1RA_0RE0RD_1LA0LE_1LF1RC_0LD0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt590: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RE0RB_1LB1LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt591: ~halts (TM_from_str "1RB1RA_1RC---_1LD0RE_1LF1LC_0LD1RC_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt592: ~halts (TM_from_str "1RB0RC_1LC0LF_1LD0LB_0RD0LE_1RA---_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt593: ~halts (TM_from_str "1RB1RA_0LC---_1LE1LD_1LC0RF_1RA0LF_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt594: ~halts (TM_from_str "1RB0LF_0RC1LD_1LA1RF_---1LE_0LA0LB_0RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt595: ~halts (TM_from_str "1RB0LE_1LC0RC_1RE1RD_---1RE_1LA0LF_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt596: ~halts (TM_from_str "1RB0RE_1LC0RA_0RF0LD_1LA1RA_1RC0LB_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt597: ~halts (TM_from_str "1RB1RD_1RC1RA_1LD0LE_0LF0LC_1LD0RD_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt598: ~halts (TM_from_str "1RB1LF_0RC0RA_1RD0RA_1LE---_1LA1LD_0LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt599: ~halts (TM_from_str "1RB1LA_1LC0RE_0LE0LD_1LA1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt600: ~halts (TM_from_str "1RB0LD_1RC0RF_1LA---_1LA0LE_1LD1LB_1RE0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt601: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LF1LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt602: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LA_0LB0LF_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt603: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1LE0LB_1RF1LE_1LE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt604: ~halts (TM_from_str "1RB1RA_1RC0RF_0LD0RA_0RE0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt605: ~halts (TM_from_str "1RB1LF_1RC0RA_0RD0RB_1LE---_1LB0LC_0RF0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt606: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD0RB_0LE---_1LF0RE_1LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt607: ~halts (TM_from_str "1RB1RE_1LC0RA_1LE0LD_1LA1RC_0LB0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt608: ~halts (TM_from_str "1RB1LD_1LC0LE_1RC0RA_1LA0LB_---0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt609: ~halts (TM_from_str "1RB1LE_0RC1LE_1LD0RF_0RA0LE_0LA1RD_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt610: ~halts (TM_from_str "1RB1LE_1LC0LC_1RF0RD_1RA1LE_1LA0LB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt611: ~halts (TM_from_str "1RB1LF_0LC1LC_1RE0RD_1LE1RA_0RA---_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt612: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LC_0RE0LB_0LF0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt613: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE0LC_1LA0LC_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt614: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---1RF_1RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt615: ~halts (TM_from_str "1RB1LF_0RC---_1LD0RE_1LD0LA_1RD1RE_0LB1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt616: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF0RD_---0LE_1LB---_1LF0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt617: ~halts (TM_from_str "1RB0RE_1LC0RF_1RA0LD_1LC0LB_1RD0RC_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt618: ~halts (TM_from_str "1RB0LE_1LC0RD_0LD0LC_1LA0RE_1RF0LE_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt619: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD0LE_---0RE_1LF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt620: ~halts (TM_from_str "1RB0LF_1LC0RE_1RA1LD_0LC1LF_---1RA_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt621: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_1LE0RB_1RC1LF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt622: ~halts (TM_from_str "1RB1LA_1LA0RC_1RD1RC_1LE0LA_---1LF_0RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt623: ~halts (TM_from_str "1RB1RE_1LC1LD_1RA0LD_0LB1RF_1RA1RB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt624: ~halts (TM_from_str "1RB1RC_1RC0RA_0LD1LD_1RF1LE_0LD0LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt625: ~halts (TM_from_str "1RB1LA_1LC1LD_1RF1RD_1RE0LB_---0RC_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt626: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_0RA0LB_1LC0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt627: ~halts (TM_from_str "1RB1LE_0RC---_1LD0RF_1LA1RF_0LA1LC_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt628: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_1LE---_0LA0LB_1RC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt629: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LC0LF_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt630: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LE0LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt631: ~halts (TM_from_str "1RB0RC_1LC1LF_1RD0LB_---0RE_1RB1RA_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt632: ~halts (TM_from_str "1RB1LD_1RC1LB_1LD0RF_---0LE_1LF1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt633: ~halts (TM_from_str "1RB1LC_1LB0RC_1LE0RD_0LE0RF_1LA1LD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt634: ~halts (TM_from_str "1RB0RE_1LC0RA_1LF0LD_1LA---_1RB0LC_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt635: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RF_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt636: ~halts (TM_from_str "1RB1LA_1LC0RE_1LA0LD_1LA1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt637: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_1RC0LC_1LA0RA_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt638: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD1RE_1LD0LA_0LF0RD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt639: ~halts (TM_from_str "1RB0RF_1LC0RA_1LA1RD_1RB1LE_---0LC_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt640: ~halts (TM_from_str "1RB1RF_1LC0LD_1RD0LB_0RF0RE_1RA---_0LB1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt641: ~halts (TM_from_str "1RB1RF_1LC0LA_0RE0LD_1LB1LD_---0RA_1RB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt642: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt643: ~halts (TM_from_str "1RB0LC_1LA0RD_1LA0LE_1RE0RC_1LC1LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt644: ~halts (TM_from_str "1RB0LB_0RC0LD_1LA1RE_1RB1LB_1RC0RF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt645: ~halts (TM_from_str "1RB0RF_1RC0LD_1LB0RA_0RB0LE_1LD0LE_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt646: ~halts (TM_from_str "1RB0LD_1RC0RD_0LA0RF_---1LE_1LB1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt647: ~halts (TM_from_str "1RB1RD_0RC1RB_1LD0RF_0LE1LC_1RA0LD_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt648: ~halts (TM_from_str "1RB1RF_1LC1LB_1LD1RC_1RE0LB_1LB0RA_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt649: ~halts (TM_from_str "1RB1RA_1RC0RF_1LD0RA_1LB1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt650: ~halts (TM_from_str "1RB0LE_1RC---_1RD0LA_1RE1RB_1LC0LF_1LC0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt651: ~halts (TM_from_str "1RB---_1LC1LF_1RE0LD_0LB1RF_0RA1RE_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt652: ~halts (TM_from_str "1RB0RD_1LC---_0RD1LB_1RF1LE_0LD1LA_0RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt653: ~halts (TM_from_str "1RB0LD_1RC0LA_1RD0RF_1LB0LE_1LB0RA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt654: ~halts (TM_from_str "1RB1RE_0RC1RA_1LD1RB_0LE0LC_1LF0LC_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt655: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD1RE_0LA1LA_0RC0RD_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt656: ~halts (TM_from_str "1RB0RB_1RC1LE_1LD1LE_1RF1LC_0LC1RA_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt657: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0LC0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt658: ~halts (TM_from_str "1RB1RF_1LC0RE_---1LD_1RB1LC_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt659: ~halts (TM_from_str "1RB0LC_0RC0RF_1RD1LC_1RE0RE_1LA1RE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt660: ~halts (TM_from_str "1RB0LC_1LA1RC_1RD0LE_1RB1RE_0RD0LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt661: ~halts (TM_from_str "1RB0RE_1LC1RB_0RA0LD_1LC1LD_1LA1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt662: ~halts (TM_from_str "1RB1RF_1RC1LD_1LD0LE_1RA0LC_1LD0RA_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt663: ~halts (TM_from_str "1RB0RE_1LC1RB_1RA0LD_1LB1LD_---1RF_1RD1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt664: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0RF0LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt665: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RE0RC_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt666: ~halts (TM_from_str "1RB0RC_1LC1LE_1RD0LB_---0RA_1LF0RF_0RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt667: ~halts (TM_from_str "1RB0RC_1LC0LF_0LE0RD_0LB1LD_1RA---_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt668: ~halts (TM_from_str "1RB1RA_0RC---_0LD1RF_1LE1LF_1RA0LC_1LD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt669: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD0RA_1LE1RC_0LA1RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt670: ~halts (TM_from_str "1RB---_1RC0LF_0RD1RA_1LE1RB_0LB0LF_0LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt671: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LF0LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt672: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_0LA0LD_0LA1RB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt673: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0RD0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt674: ~halts (TM_from_str "1RB1RE_1LC0RF_1LD1LC_0RE---_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt675: ~halts (TM_from_str "1RB0LC_0RC0RF_1LD1RD_1RE1LA_1LA1LE_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt676: ~halts (TM_from_str "1RB1LE_0RC1RA_1RD0RA_1LA0RE_1LC0RF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt677: ~halts (TM_from_str "1RB0LB_1LA1LC_1LA1RD_0LB1RE_0RF1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt678: ~halts (TM_from_str "1RB1LA_1RC0RF_0LD1LD_1RF1LE_---0LC_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt679: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RF_1LE---_1LB0LC_1RC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt680: ~halts (TM_from_str "1RB1LD_1RC0LE_0LA0RA_0LF1LE_0LB0RB_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt681: ~halts (TM_from_str "1RB1LA_1LC0RF_---0LD_0LE1LE_1RF1LC_1RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt682: ~halts (TM_from_str "1RB1LE_1RC0LA_1RD1LC_0LB0RF_---1LB_1RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt683: ~halts (TM_from_str "1RB0LB_1RC0RF_1LD1LE_1LF0LC_1LA---_1RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt684: ~halts (TM_from_str "1RB1LB_1LC1LF_1RD0RA_1LA0RE_1RC1RE_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt685: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_0LA0LE_---1LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt686: ~halts (TM_from_str "1RB0LE_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt687: ~halts (TM_from_str "1RB0RB_1RC1LE_1LD0LF_1RA0RB_1LB0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt688: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_1RD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt689: ~halts (TM_from_str "1RB1LD_1RC0LE_0LA0RA_0LF1LE_0LB0RB_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt690: ~halts (TM_from_str "1RB1LE_0RC0RF_1LD1RB_1RA0LC_---0LD_0LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt691: ~halts (TM_from_str "1RB0RC_1LC0LF_1LD0LB_1RE---_1RA1RB_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt692: ~halts (TM_from_str "1RB0LB_1RC---_1LD0RC_0RF0RE_0LA0LF_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt693: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0RB0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt694: ~halts (TM_from_str "1RB1LD_1RC0LA_0RD0RF_1LE0RE_0LB0LA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt695: ~halts (TM_from_str "1RB0RC_1LC0LE_1RD0LB_1RE0RA_1LC0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt696: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt697: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0RE0LE_---1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt698: ~halts (TM_from_str "1RB1RF_1RC0RA_1LD0LE_1LA0LC_1LD0RD_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt699: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0RA0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt700: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt701: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA1LF_1LF0LE_0LB---_0LA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt702: ~halts (TM_from_str "1RB0RE_1LC0RA_1LA0LD_1LA1RA_1RF0LB_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt703: ~halts (TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_1LF---_1LD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt704: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_0RB1LE_---1LD_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt705: ~halts (TM_from_str "1RB0RA_0LC0LE_0RD1LB_1RA---_0LF0RD_1LC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt706: ~halts (TM_from_str "1RB0LA_1RC0RF_1RD0LA_1LE---_0LF0LE_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt707: ~halts (TM_from_str "1RB1RF_1LC0RA_---1LD_0LE1LB_1LA1LA_1RB1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt708: ~halts (TM_from_str "1RB0LC_0RC1RB_1LD0RA_0LE---_1LB1LF_0RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt709: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_0LE1LD_0RC1RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt710: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1LC1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt711: ~halts (TM_from_str "1RB0LF_1RC1RA_1RD0RF_0LE---_0LA1LE_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt712: ~halts (TM_from_str "1RB0LE_0RC1RA_1RD1RE_1LA1LE_0LD0RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt713: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE1RF_1LE0LB_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt714: ~halts (TM_from_str "1RB0LC_0RC0RB_0RD1RC_1LE1LF_1RF---_1LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt715: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA1RD_1LD1RF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt716: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE0LC_1LA0LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt717: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LB_1RF0LC_1RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt718: ~halts (TM_from_str "1RB1LC_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt719: ~halts (TM_from_str "1RB0LC_0RC0RB_0RD1RC_0LE1LF_1LF---_1LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt720: ~halts (TM_from_str "1RB0RF_1RC0RA_1LD1LE_1LA0LC_1LF---_1RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt721: ~halts (TM_from_str "1RB1LC_1RC0RC_1RD1LE_1LA0LF_1LC0LD_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt722: ~halts (TM_from_str "1RB1LE_0LC1RD_1RB1LC_1RB1RE_1RF0LA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt723: ~halts (TM_from_str "1RB0LE_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt724: ~halts (TM_from_str "1RB1RF_1LC0RE_1LD1LC_1LE---_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt725: ~halts (TM_from_str "1RB1LA_0LC0RE_0LE0LD_1RE1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt726: ~halts (TM_from_str "1RB0RC_1LC0RA_1RF0LD_1LE0RC_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt727: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD0LE_---0RE_1RF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt728: ~halts (TM_from_str "1RB0LB_1LC1LF_1RE1RD_0RC1LA_1LD0RD_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt729: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1RD_0RB0LC_0LA1LB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt730: ~halts (TM_from_str "1RB0RC_1LA0RA_1RD0LD_1LE0RF_1LA0LB_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt731: ~halts (TM_from_str "1RB0RD_1LC0LF_---0LD_1RE0LB_1RA0RE_1LD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt732: ~halts (TM_from_str "1RB0LF_1RC0RA_0RD0RB_1LE---_1LB0LC_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt733: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LF_1RA0LC_0RC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt734: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE0LC_1RA0LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt735: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1RB1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt736: ~halts (TM_from_str "1RB1RE_1LC1RB_0RB1LD_1LC1LE_1LF0RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt737: ~halts (TM_from_str "1RB0RE_0RC0RF_1RD0LE_1RE0RA_1LC0LE_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt738: ~halts (TM_from_str "1RB1RE_1LC0RE_0LD1LB_1LA1LE_0RA1LF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt739: ~halts (TM_from_str "1RB---_1LC0LF_1RD0LB_---0RE_1RF0RB_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt740: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_0LE1LB_1LD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt741: ~halts (TM_from_str "1RB0LF_1LB0RC_1RA0LD_1LE---_0LC1LF_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt742: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_1RE0LF_1RA1RE_1RE1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt743: ~halts (TM_from_str "1RB0LD_0LC0RE_1RD0LD_1LA0RC_0RF---_1LB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt744: ~halts (TM_from_str "1RB---_1LC1RF_0LD1RC_1LA1LE_1LD1LF_1LC0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt745: ~halts (TM_from_str "1RB1LC_0LA0RD_0LD1LF_1RE---_1RB0LF_0LE0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt746: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD1RC_---0RE_1RF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt747: ~halts (TM_from_str "1RB0LC_1LA1LC_0LB1RD_0RC1RE_0RF---_0RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt748: ~halts (TM_from_str "1RB1LE_0LC1RD_1RB1LC_1RB1RE_1RF0LA_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt749: ~halts (TM_from_str "1RB1LD_1LC0RE_---0LD_1LE0LB_1RB1RF_0LB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt750: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA1LE_---1LF_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt751: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA1RD_1RD1RF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt752: ~halts (TM_from_str "1RB0LD_1RC1RB_0LD---_0LF1RE_1LF0RD_1LA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt753: ~halts (TM_from_str "1RB0RC_1LB1RA_1LD1RB_0LE0LC_1RA1LF_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt754: ~halts (TM_from_str "1RB0LC_1LC0RF_1LE1LD_1LC---_1LF1RB_1RB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt755: ~halts (TM_from_str "1RB1RA_1LC1RD_1RE0LD_1RA0LC_0RF0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt756: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt757: ~halts (TM_from_str "1RB1LE_1LC0RA_1LE1RD_---0RB_0LA0LF_0RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt758: ~halts (TM_from_str "1RB0RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt759: ~halts (TM_from_str "1RB---_1RC0LF_0LD0RD_1RB1LE_0LA1LF_0LB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt760: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LE0LC_1RA0LC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt761: ~halts (TM_from_str "1RB0RD_1RC0RF_1RD0LC_1LE0RF_---1LC_1RA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt762: ~halts (TM_from_str "1RB1RF_1RC1RA_1LD0LE_1RB0LC_1LD0RD_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt763: ~halts (TM_from_str "1RB0RC_0RC0RF_1LD1LE_0LC---_1LA0LA_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt764: ~halts (TM_from_str "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---1RF_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt765: ~halts (TM_from_str "1RB---_1RC1RE_0LC0RD_1LA0LE_1LD0LF_1LE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt766: ~halts (TM_from_str "1RB0LC_0LC0RE_1LA1LD_0RA0RF_1RC0RF_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt767: ~halts (TM_from_str "1RB1RE_1RC1LE_1LD1LA_1RF1LC_0LC0RB_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt768: ~halts (TM_from_str "1RB0RC_0LA0LF_1RD0RB_1LE0RA_1LC1LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt769: ~halts (TM_from_str "1RB1LD_0LC0RE_---1LD_1LA0LB_1RF1RD_0RA1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt770: ~halts (TM_from_str "1RB1RA_1LC1RE_---1LD_0LE1LB_0RF0LB_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt771: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_1RE1LF_1RA1RE_1LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt772: ~halts (TM_from_str "1RB0LF_1RC0RA_0LD1LD_1RF1LE_0LD0LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt773: ~halts (TM_from_str "1RB0RC_1LC0RA_0RF0LD_1LE0RC_1LA1LD_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt774: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_0LA0LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt775: ~halts (TM_from_str "1RB0LE_1LC1RE_0RD1RC_1LE0RF_0LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt776: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD1RC_---0RE_1LF0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt777: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA1LE_---0LF_0RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt778: ~halts (TM_from_str "1RB---_1RC1RF_0LD1RE_0RA0LC_1LD0RD_0RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt779: ~halts (TM_from_str "1RB0RC_1LC0LE_1LD0LB_1RE---_1LC0RF_1RA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt780: ~halts (TM_from_str "1RB0LC_0LC0RD_0RD1LA_1RE0RF_1LF1RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt781: ~halts (TM_from_str "1RB1RC_0LC0RA_0RF1LD_1LE0LA_1LC1LB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt782: ~halts (TM_from_str "1RB1RA_1RC0LD_1LB0LF_---0LE_0LF1LB_1RF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt783: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA1RB_1RF0LC_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt784: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD1LC_0LA0RB_---1LF_0RF1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt785: ~halts (TM_from_str "1RB0LC_1LA0RF_1LD1LD_0LE0LA_1RA1RE_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt786: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB0RF_1LB0RC_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt787: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD0LA_0LF1LA_0RC1RE_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt788: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD1LF_1LA0LA_1LB1LA_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt789: ~halts (TM_from_str "1RB0LE_1LC1RA_---0RD_1RF1RE_0LF1RC_1LA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt790: ~halts (TM_from_str "1RB1LC_1LC0LF_1RD0LB_1RA1RE_1RD---_1LC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt791: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA0LF_1RB0LC_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt792: ~halts (TM_from_str "1RB1LC_1LB0LC_1LD1RE_1RB1RF_1RC0RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt793: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE0LF_0LA1LD_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt794: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt795: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD0LE_---0RE_1LF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt796: ~halts (TM_from_str "1RB0RC_1LC0LF_0LE1RD_---1LE_1RA0LB_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt797: ~halts (TM_from_str "1RB1RE_0LB1LC_1LD0RE_0LE0LB_1RF0LC_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt798: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LF1LB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt799: ~halts (TM_from_str "1RB0RE_1LC---_1LD1LC_1LE0LA_1RA0RF_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt800: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_1RC1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt801: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LB_1LF0LC_0RF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt802: ~halts (TM_from_str "1RB0RB_0LC0RE_1RA1LD_1LC0LF_1LB1RB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt803: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1RF1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt804: ~halts (TM_from_str "1RB0LE_1LC---_0LD0LC_1LE0RE_1RF0LE_1RA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt805: ~halts (TM_from_str "1RB---_1LC0LE_1RF0LD_0RE1RD_1LA1LB_0RD0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt806: ~halts (TM_from_str "1RB1RE_1LC0LF_0RE0LD_1LB1LD_---0RF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt807: ~halts (TM_from_str "1RB1LF_1RC0LA_1RD0RB_1RE1LD_1LB0RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt808: ~halts (TM_from_str "1RB1RD_0LC1RA_1RA1LB_1LD0RE_---1RF_1LF0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt809: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_0RF0LC_1RF0RA_1LB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt810: ~halts (TM_from_str "1RB1RF_0RC1RC_1LD0LA_0LE---_1LF1LE_0RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt811: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE1RF_1LE0LC_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt812: ~halts (TM_from_str "1RB0RC_1LC0LD_1RF0LD_1LE0RB_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt813: ~halts (TM_from_str "1RB1RC_1LC1RE_---0LD_1LA1LE_1LA1RF_1RE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt814: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RE_1LE1LD_0RB---_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt815: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---1RF_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt816: ~halts (TM_from_str "1RB---_1LC0RE_1LD0LB_0LE0LC_1RF0LA_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt817: ~halts (TM_from_str "1RB0RE_1LC0RA_1LA0LD_1LA1RA_1RF0LB_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt818: ~halts (TM_from_str "1RB0LC_0LC0RB_0RD1LA_1RE0RF_1LF1RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt819: ~halts (TM_from_str "1RB0LF_0LC0RD_1LE1RD_0RC1LB_0LA0LC_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt820: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_0LF1LB_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt821: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE1LF_0LA1LD_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt822: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD1RB_0LA0LE_1LA1LF_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt823: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1LC1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt824: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB1RF_1LB0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt825: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1RE0LB_1RF1LE_1LE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt826: ~halts (TM_from_str "1RB1RC_0LC0RC_0RA1LD_1LC1LE_1RE0LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt827: ~halts (TM_from_str "1RB1RD_1RC1RA_1LA1LC_1RF0LE_1LC1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt828: ~halts (TM_from_str "1RB1RE_1LC0LD_1RD0LB_0LF0RE_1RA1LF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt829: ~halts (TM_from_str "1RB1RA_0RC0LD_1LC1RB_---0LE_0LF1LB_1RF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt830: ~halts (TM_from_str "1RB0LF_0RC0RD_0RD---_1RE0RF_1LF1LB_1LA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt831: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA1LF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt832: ~halts (TM_from_str "1RB0RE_0LC1RD_1LE1LD_1LB1RA_0RD1RF_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt833: ~halts (TM_from_str "1RB0LF_1LC0LE_0LD0LB_1RA---_1LB0RD_0RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt834: ~halts (TM_from_str "1RB0LC_1LA0RD_1LB0LF_0LB0RE_1RD0RE_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt835: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB1LF_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt836: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LF0RD_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt837: ~halts (TM_from_str "1RB---_0LC0LE_1RF1LD_1LE1RB_0LB0RC_0RA1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt838: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA1RD_1RD0RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt839: ~halts (TM_from_str "1RB1LD_1RC1LF_0RD1RD_1RE0LA_0LF0RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt840: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LB0LE_---1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt841: ~halts (TM_from_str "1RB1LD_1RC1LB_0LD0RF_0RE0LE_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt842: ~halts (TM_from_str "1RB0RD_1RC0RC_1LD1RF_---0LE_1LB1LE_1RA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt843: ~halts (TM_from_str "1RB0RE_0LB1LC_1LD0LA_0LE0LC_1RF---_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt844: ~halts (TM_from_str "1RB0RC_0LC1RA_1RD1LC_1RF0LE_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt845: ~halts (TM_from_str "1RB---_1LC0RC_1RA1LD_0LE1LB_0RA0LF_1RE1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt846: ~halts (TM_from_str "1RB0RE_1RC0LB_1LD0RE_---1LB_1RF1RF_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt847: ~halts (TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_1RF---_0LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt848: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LA0LB_1RF0LF_0LD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt849: ~halts (TM_from_str "1RB---_1RC0LF_0RD1RA_1LE1RB_0LB0LF_1LE0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt850: ~halts (TM_from_str "1RB1RE_1LC1RA_1RA0LD_0RB0LF_---0LF_1RD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt851: ~halts (TM_from_str "1RB0RD_0RC0LF_1RD1RC_1LE1RA_0LA1LB_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt852: ~halts (TM_from_str "1RB1RC_1LC0LE_---0LD_1LA1LE_1LA1RF_1RE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt853: ~halts (TM_from_str "1RB0LA_0RC---_0RD0RA_1LD0LE_1RF1LE_0LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt854: ~halts (TM_from_str "1RB1LA_1RC0RF_0LC1RD_1RE0RE_1LE0LA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt855: ~halts (TM_from_str "1RB1LC_1LC0RE_1RD0LD_1LE0LF_1RB0RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt856: ~halts (TM_from_str "1RB1RD_1RC1RA_1LD0LE_0RF0LC_1LD0RA_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt857: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE1RF_1LE0LB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt858: ~halts (TM_from_str "1RB1RA_0RC0LF_0RD0LC_1LE0RA_1LB---_1RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt859: ~halts (TM_from_str "1RB1LE_1LC0RA_0RD1LB_---1RA_0LA0LF_1RC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt860: ~halts (TM_from_str "1RB---_1RC1LF_0LD1RE_0RA0LC_1LD0RD_0RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt861: ~halts (TM_from_str "1RB0RC_1RC---_1RD0RE_1LE0LF_1RA0LD_1LE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt862: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0LF0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt863: ~halts (TM_from_str "1RB1LE_1RC0LF_1RD1RB_1LE0RF_---1LA_0RC1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt864: ~halts (TM_from_str "1RB0LE_1RC0LA_1RD1LC_0LB0RF_---1LB_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt865: ~halts (TM_from_str "1RB0RC_0RC0LD_1LD1RE_0LA0LF_1RA1RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt866: ~halts (TM_from_str "1RB0LE_1RC0RF_0RD1RA_1LE0LA_0LA1LA_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt867: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1RE0LB_1RF1LE_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt868: ~halts (TM_from_str "1RB1RD_1RC1LF_0RD0RB_1LE1RA_1LF---_0LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt869: ~halts (TM_from_str "1RB0RF_1LC1RA_1RE0RD_0RB0LE_1LD0LA_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt870: ~halts (TM_from_str "1RB1RF_1LC1RB_1RE0LD_1LB1LD_---0RA_0RB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt871: ~halts (TM_from_str "1RB0RE_0LC0RF_1RA1LD_1LC1LE_---0RF_1LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt872: ~halts (TM_from_str "1RB1RC_1LC1RE_1RF0LD_1LA1LB_1LC0RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt873: ~halts (TM_from_str "1RB1LE_0RC1RD_1RD---_0LA0LF_1LF0LB_0LD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt874: ~halts (TM_from_str "1RB0LB_0RC1RF_1LD0RE_0LA0LD_1RC---_0RA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt875: ~halts (TM_from_str "1RB0RC_1LA0RA_1RD0LD_1LE1RF_1LA0LB_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt876: ~halts (TM_from_str "1RB0LB_0RC1RF_1LD0RE_0LA0LD_1RC---_0RA0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt877: ~halts (TM_from_str "1RB0RC_1LC0LE_1RD0LB_0RE0RA_1LC0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt878: ~halts (TM_from_str "1RB---_0RC0RE_1LD---_1LE0LB_1RB0RF_1RE0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt879: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RE0RC_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt880: ~halts (TM_from_str "1RB1LA_1LC0RF_---0LD_0LE1LE_1RF1LC_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt881: ~halts (TM_from_str "1RB---_1LC0LE_1LD0LB_1RE0LF_0RA0RF_1RD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt882: ~halts (TM_from_str "1RB1LE_0RC0RF_1LD1RB_1RA0LC_---0LD_1RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt883: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RB0LB_1RC0RF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt884: ~halts (TM_from_str "1RB0LF_1RC1LE_0RD1RA_1LA0RE_0LA0RB_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt885: ~halts (TM_from_str "1RB0LE_1RC0RD_1LD1LF_1RF0LA_1LC---_1LC0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt886: ~halts (TM_from_str "1RB0RE_1LC1RB_1LA0LD_0LE1LD_1RF0RB_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt887: ~halts (TM_from_str "1RB0RC_1LC1RD_1RA0LD_1RA0LE_1RD0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt888: ~halts (TM_from_str "1RB0RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt889: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD0RA_0LE1LA_---1RC_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt890: ~halts (TM_from_str "1RB1RD_1LC1LF_1RC0RD_1RB1LE_1LD0LB_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt891: ~halts (TM_from_str "1RB1LE_0RC0LA_1RD---_1LA0RF_0LB1LD_1RC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt892: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_1RD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt893: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE1RF_1LE0LB_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt894: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE0LF_1RE0RC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt895: ~halts (TM_from_str "1RB0RA_1RC0LC_1LD1LF_---0LE_1RB0LF_0LB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt896: ~halts (TM_from_str "1RB0RC_1LC0LD_1RB0LB_1LE0RE_1RA1LF_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt897: ~halts (TM_from_str "1RB1RE_1LC0LC_1RD1LC_---0RE_1LF1RA_0LB1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt898: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_1RF0LC_1LD0RA_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt899: ~halts (TM_from_str "1RB---_1RC1RA_1RD0RE_1LE0LF_1RB0LD_1RD0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt900: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0LC0LC_1RA---_0RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt901: ~halts (TM_from_str "1RB1RD_1LC0LE_1RE0RD_1RA0LC_1LF0RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt902: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1RC0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt903: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF0RD_---0LE_1LB0LB_1LE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt904: ~halts (TM_from_str "1RB1RF_0LC1LB_1RE0LD_1LB0RA_0RA---_0LF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt905: ~halts (TM_from_str "1RB1LC_0RC0RA_1LD0RF_1LE---_0RB0LA_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt906: ~halts (TM_from_str "1RB0RC_1LC1LE_1RA0RD_1RA0LE_1LB1LF_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt907: ~halts (TM_from_str "1RB0RF_0RC0RE_0RD---_1LA1LD_0RF1RB_1LF0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt908: ~halts (TM_from_str "1RB1LE_0RC1RF_1LD0RD_1RC1RA_---1LF_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt909: ~halts (TM_from_str "1RB1LD_1RC1LB_1LD0RF_---0LE_1RA1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt910: ~halts (TM_from_str "1RB1LF_0LC1RE_0RD0LB_1RA---_1LC0RC_0RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt911: ~halts (TM_from_str "1RB1RE_1LC0LF_1RD0LB_1RB1LA_---0RA_1LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt912: ~halts (TM_from_str "1RB1RE_1LB0LC_1LA1RD_1RC0RA_---0LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt913: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_0RE1RE_1LF0LA_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt914: ~halts (TM_from_str "1RB1RA_0LC0RA_1LE0LD_1RC1LB_---1LF_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt915: ~halts (TM_from_str "1RB0LE_1RC---_1RD1RC_1LA0LF_0LF1LA_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt916: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_---1LE_0LF1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt917: ~halts (TM_from_str "1RB0RF_0LC0RA_1LE1RD_0RC---_1LA0LB_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt918: ~halts (TM_from_str "1RB---_1RC0LF_0LD0RA_1LE0RC_0LA1LF_0LB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt919: ~halts (TM_from_str "1RB---_0RC0RE_1LD1RB_0LE0LC_1RF0LC_0LF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt920: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_0LE1LB_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt921: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_0RE0LF_0LC1RD_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt922: ~halts (TM_from_str "1RB1RF_1LC0LD_1RD0LB_1LC0RE_1RA---_0LB1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt923: ~halts (TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RF_0LE1RA_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt924: ~halts (TM_from_str "1RB0RB_0LC0LE_0RA1LD_1LC---_1LF1RC_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt925: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---1LE_1RB0LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt926: ~halts (TM_from_str "1RB0RE_1LC1RE_1LB0LD_1LA0LF_1LA1RB_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt927: ~halts (TM_from_str "1RB0RA_1LC0RA_1LA0LD_1LE0LF_0LB0LE_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt928: ~halts (TM_from_str "1RB0RA_0LC0RA_1LD0RB_1RC0LE_1LC0LF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt929: ~halts (TM_from_str "1RB0RC_1LC0RA_0LD1LB_1RE0LE_0RB1LF_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt930: ~halts (TM_from_str "1RB1LD_1LC0LE_0LD0LB_1RA1RF_1LB0RD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt931: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RD_0RB1LE_---1LD_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt932: ~halts (TM_from_str "1RB1LF_0RC0RA_1LD0RD_1LE---_1RF1LA_0LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt933: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1RE0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt934: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE1LD_0LB1LE_1LF0RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt935: ~halts (TM_from_str "1RB0RB_0RC1LD_1LD1RB_0LE0LC_1RA0LF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt936: ~halts (TM_from_str "1RB1LD_1RC1LB_0LD0RF_1RB0LE_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt937: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_0RE1RF_1RD1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt938: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_0LF0RD_1LB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt939: ~halts (TM_from_str "1RB0LE_1LC1RE_0LD1LB_1LA0LB_1RD0LF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt940: ~halts (TM_from_str "1RB1RF_1LC0RA_---1LD_0LE1LB_1LF1LA_1RB1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt941: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD0RB_0LD0RE_1LF---_1LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt942: ~halts (TM_from_str "1RB0LB_1LA0LC_1LD1RA_0RE1RB_1RF1LE_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt943: ~halts (TM_from_str "1RB0LF_0LC0RB_0RE1LD_0LE1LF_1RA---_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt944: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE---_1LF0LC_1RC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt945: ~halts (TM_from_str "1RB0LE_1RC1LB_1LD1RE_---0LA_1RA0RF_0LC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt946: ~halts (TM_from_str "1RB0LE_1LC0RA_0LD0LC_1RE0LE_0RB0LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt947: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1LE1LF_1RA1RE_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt948: ~halts (TM_from_str "1RB0RE_1LC---_1RD1LB_0LE1LA_1RF1LD_0RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt949: ~halts (TM_from_str "1RB0RD_1RC0RF_1LD1RA_---0LE_1LA1RC_1RF1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt950: ~halts (TM_from_str "1RB0RB_1LC0LD_---0LD_0LE1RF_1RF1LD_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt951: ~halts (TM_from_str "1RB0RF_0RC1RF_1LD---_0LE0RE_1LA0RC_0RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt952: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_0RB0RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt953: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE0LF_1RE0RC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt954: ~halts (TM_from_str "1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1LC0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt955: ~halts (TM_from_str "1RB0LE_1LC1LF_1RD0LB_---1RE_0RA1RC_1LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt956: ~halts (TM_from_str "1RB1LD_0RC1RE_1LD0RF_1LE1LF_0LA1LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt957: ~halts (TM_from_str "1RB0RE_1LC0RA_1LE1LD_1LB---_1RB0RF_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt958: ~halts (TM_from_str "1RB1LC_0RC0RE_1LD0RB_0LA1LF_1RB0RA_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt959: ~halts (TM_from_str "1RB1RF_1RC1RA_1LD0LE_1RB0LC_1LD0RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt960: ~halts (TM_from_str "1RB1RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt961: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_0RB1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt962: ~halts (TM_from_str "1RB1LA_1LC0RC_1LE1RD_0LA1RC_0LD1LF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt963: ~halts (TM_from_str "1RB1RF_1LC1RB_1RE0LD_1LB1LD_---1RA_1RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt964: ~halts (TM_from_str "1RB1RD_0LC1RA_1RD1LC_1RF0LE_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt965: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_0RA0LE_0LA1RD_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt966: ~halts (TM_from_str "1RB0RC_1LC0LF_1LD0LB_0RE---_1RA0LE_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt967: ~halts (TM_from_str "1RB1LC_0LC---_1LE1RD_1RC0RE_0RF1RF_1LB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt968: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LE0LC_1RA0LC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt969: ~halts (TM_from_str "1RB1LC_0RC0RE_1LD0RE_0LA1LF_1RB0RA_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt970: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LE0LB_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt971: ~halts (TM_from_str "1RB0RE_1LC1RB_1RE0LD_1LB1LD_1RB1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt972: ~halts (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA0RF_0RB---_0RD0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt973: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD1RB_1LB0LC_---1LF_0RD0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt974: ~halts (TM_from_str "1RB1LF_0RC---_1RD0RE_0LE1LA_1RC1LF_0LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt975: ~halts (TM_from_str "1RB0RC_1LC0LC_0RE0RD_1RA1LE_0LB1RF_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt976: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LE1LF_1RB0RA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt977: ~halts (TM_from_str "1RB0LD_1LC1RC_---1RA_1LF1RE_0RD1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt978: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA0RF_1LA1RB_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt979: ~halts (TM_from_str "1RB0RD_1LC1LE_0LD1LB_1RE1LC_0RA1LF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt980: ~halts (TM_from_str "1RB0LE_1RC1RE_0RD1RC_1LE0RF_0LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt981: ~halts (TM_from_str "1RB0LB_1LC0RD_1LD1LB_1RB0RE_---1RF_1LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt982: ~halts (TM_from_str "1RB0LE_1RC1RE_0RD0LF_1LE0RF_0LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt983: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RE0RC_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt984: ~halts (TM_from_str "1RB0LD_1LC1RC_---1RA_1LF1RE_0RD0RF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt985: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB0RF_1LB0RC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt986: ~halts (TM_from_str "1RB1LE_0LC0RC_1RD0LB_0LA0RF_0LF1LB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt987: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_0LF0LC_1LC0RF_1RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt988: ~halts (TM_from_str "1RB---_0LC0LD_1RF1LA_1LB0LE_1LD0RC_1RD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt989: ~halts (TM_from_str "1RB0RE_0RC---_1RD1LF_0LA1LA_1LF1RC_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt990: ~halts (TM_from_str "1RB0RC_1LB1RA_1LD1RB_0LE0LC_1RA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt991: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1LE1LF_1RA1RE_1RA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt992: ~halts (TM_from_str "1RB0LB_0LC1RE_1LA1LD_0LC1LC_0RB0RF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt993: ~halts (TM_from_str "1RB0LD_0LC0RE_---1RD_1LA0LF_1RF0RD_1LD1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt994: ~halts (TM_from_str "1RB0RA_1LC0RA_1LD0LC_1LE0LF_1RA0LB_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt995: ~halts (TM_from_str "1RB0RF_1RC1RE_1LD0LD_0RB1LC_0LF0RA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt996: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD1LC_0LA0RB_---1LF_1RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt997: ~halts (TM_from_str "1RB---_0RC0LC_1RD0LA_1LE0LF_0LA1LF_0LD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt998: ~halts (TM_from_str "1RB1LC_1LA0RD_1LA1LD_---0RE_1LF1RF_0LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt999: ~halts (TM_from_str "1RB0LB_0LC1RA_1RE1RD_0LE1RF_1LA1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1000: ~halts (TM_from_str "1RB0LE_0RC0RB_1LD0RD_0LA1LF_1LA---_0LC1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1001: ~halts (TM_from_str "1RB1LF_1RC0RE_1RD1LC_1LE0RB_0LA1LA_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1002: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1003: ~halts (TM_from_str "1RB1RF_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1004: ~halts (TM_from_str "1RB0LE_1RC1RB_1LD0RE_1LA1LC_0LD0LF_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1005: ~halts (TM_from_str "1RB1RE_1LC0LD_1LA0LB_1LF0RE_1RA1LD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1006: ~halts (TM_from_str "1RB1RE_0LC1RA_1LD1LB_0RB0LB_1LE0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1007: ~halts (TM_from_str "1RB0LC_1LC1RA_0LF1RD_---0RE_1RF1RC_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1008: ~halts (TM_from_str "1RB0LF_1LC0RA_0LE0LD_0LE1LE_1RF1LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1009: ~halts (TM_from_str "1RB1RE_1LC1LE_0RD1LB_1RE1RD_1LF0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1010: ~halts (TM_from_str "1RB1RE_1LB0LC_1RD1LC_1RA0RE_0LF0RB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1011: ~halts (TM_from_str "1RB0RC_1LC0LE_0RD0LB_1LA1RE_1RD0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1012: ~halts (TM_from_str "1RB---_1LC1RE_0RE0RD_0LF0LE_1LD1RC_1RA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1013: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE1RF_1LE0LB_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1014: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_1RC0LC_1LA0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1015: ~halts (TM_from_str "1RB1LC_0RC1LD_1LD0RF_1LE---_0RB0LA_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1016: ~halts (TM_from_str "1RB0RE_0RC0RF_1LD---_1LA0LB_1RA0LC_1RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1017: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD0RB_1LE---_1LF1LB_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1018: ~halts (TM_from_str "1RB1RC_1LC0RE_1RA0LD_1LA0LB_1LD0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1019: ~halts (TM_from_str "1RB0LF_0LC0RD_1LE1RD_0RC1LB_0LA1RD_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1020: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_1LE0RB_0LA1LA_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1021: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0RE0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1022: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1LA1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1023: ~halts (TM_from_str "1RB0LE_0RC1RF_1LD---_1LE0RF_0RA0LC_0RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1024: ~halts (TM_from_str "1RB0RE_1LC0RD_1LA0LB_1LB0RA_0RF0LD_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1025: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA1RF_1LA0LB_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1026: ~halts (TM_from_str "1RB1LD_1LC1LE_1RC0RA_1LA0LB_---0RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1027: ~halts (TM_from_str "1RB0RF_1RC0RE_0LD---_1LA1LD_0RF1RB_1LF0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1028: ~halts (TM_from_str "1RB0LF_0LC0RE_---1LD_0LE1LF_1RA---_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1029: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LE0LC_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1030: ~halts (TM_from_str "1RB1LA_1LB0RC_1RD1RC_1LE1LA_---0LF_1LE0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1031: ~halts (TM_from_str "1RB0RF_1RC0RA_0LD---_1LE0RD_1LA0LB_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1032: ~halts (TM_from_str "1RB0RE_1LC1RA_1LA0LD_0RB0LF_---1LF_1RD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1033: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_0LF1LE_---1LD_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1034: ~halts (TM_from_str "1RB0RC_1LC0LE_1RA0LD_1RC0LB_0LF0RD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1035: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_0RA0LE_0LA1RB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1036: ~halts (TM_from_str "1RB0LD_1LC1RA_1LF0RA_0RE1LA_1RC---_1LE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1037: ~halts (TM_from_str "1RB0LC_1LA0RD_1LD0LF_1RB1RE_0LB0LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1038: ~halts (TM_from_str "1RB1LA_1LA0RC_1RD1RC_1LE0LA_---1LF_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1039: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_0LE0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1040: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1LB0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1041: ~halts (TM_from_str "1RB0RC_1LC0RA_1RB0LD_1LE---_1LA1LF_0RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1042: ~halts (TM_from_str "1RB0LD_1RC1RF_1RD1LA_1LA0LE_1LA0RB_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1043: ~halts (TM_from_str "1RB1LC_1LC0RF_---1LD_0LE1LB_1LF0RD_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1044: ~halts (TM_from_str "1RB1LE_1LC0RC_1RD1RC_0LA1LF_---0LB_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1045: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA1LF_1RA1RE_1RA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1046: ~halts (TM_from_str "1RB---_1RC1RD_1LD0RF_1RB0LE_1LB0LC_1LE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1047: ~halts (TM_from_str "1RB0LC_1RC0RF_1LD0RF_---0LE_1LF1LE_1RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1048: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RA0LF_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1049: ~halts (TM_from_str "1RB0LC_0LA0RD_1LA1LE_1RC0RF_0RA0RF_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1050: ~halts (TM_from_str "1RB0RF_1LC1RA_---0LD_1RA0LE_1LF1LD_1RB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1051: ~halts (TM_from_str "1RB0LF_1LC0LA_1RD0LB_1RF1RE_1RD---_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1052: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_0LB1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1053: ~halts (TM_from_str "1RB1LD_1RC0LE_1LA0RF_0LA1LE_0LB0RB_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1054: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1RF1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1055: ~halts (TM_from_str "1RB1RE_1LC0LD_1LA0LB_0LF0RE_1RA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1056: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1057: ~halts (TM_from_str "1RB1RC_0LC0RA_0RF1LD_1LE0LA_1RA1LB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1058: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1059: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RB0LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1060: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0RE0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1061: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1RB0LF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1062: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC0LD_1LE0LF_1LA---_0LE1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1063: ~halts (TM_from_str "1RB0LD_1RC1RF_0LA1LA_1LC1RE_0RD0LF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1064: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE1LF_1LB1RD_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1065: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LF1RC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1066: ~halts (TM_from_str "1RB0LF_1LC0RD_1LA0LB_1RB0RE_0RF---_0LC1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1067: ~halts (TM_from_str "1RB1LA_0RC0RD_1LC0LA_---1RE_0RF0RC_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1068: ~halts (TM_from_str "1RB0RE_1LC1LB_1LD1RC_1RA0LB_0LA1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1069: ~halts (TM_from_str "1RB0RE_0LC1RD_1LE1LD_1LB1RA_0RD0RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1070: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1071: ~halts (TM_from_str "1RB1RA_1LC1RC_1LA1LD_0LC0LE_---0RF_1RE1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1072: ~halts (TM_from_str "1RB---_1RC0LE_0RD1RA_1LE0RB_0LF1RC_1LB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1073: ~halts (TM_from_str "1RB1LF_1RC0RD_0LD0LE_---0RE_1RF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1074: ~halts (TM_from_str "1RB1LD_0RC---_1LD0RE_0LA0LF_1RC0LB_0LE1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1075: ~halts (TM_from_str "1RB0RE_1LC0RD_1LA0LB_1LB0RA_1RF0LD_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1076: ~halts (TM_from_str "1RB1LC_0RC0LB_1LD0RF_1LE---_0RB0LA_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1077: ~halts (TM_from_str "1RB0RC_1LC0RD_1RF1LD_1LA0RE_---0LB_0RA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1078: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0RE0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1079: ~halts (TM_from_str "1RB1LA_0LC0RF_1LE0LD_1RC1LB_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1080: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE1LD_0LB1LE_1LF0RA_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1081: ~halts (TM_from_str "1RB---_1RC1RF_1LD0LE_1RE0LC_1LD0RA_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1082: ~halts (TM_from_str "1RB1RA_1RC0RD_1LD0LE_1LF0LC_1LD0RA_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1083: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RE0RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1084: ~halts (TM_from_str "1RB1RC_1LC1RE_1RF0LD_1LA1LB_0RD0RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1085: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_0RB1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1086: ~halts (TM_from_str "1RB---_1RC0LE_1RD0RB_0RE0RC_1LF1RA_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1087: ~halts (TM_from_str "1RB0RB_1LC0LF_0RF0LD_1LE1LD_0LF---_0RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1088: ~halts (TM_from_str "1RB1RD_1LC0RD_1RD1LB_0RA1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1089: ~halts (TM_from_str "1RB---_0LC0LE_1RD1LB_0RE0RC_0RF0RC_1LF0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1090: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RB0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1091: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1LF0RD_0LA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1092: ~halts (TM_from_str "1RB1RC_1LC1LD_1RA0LD_0LB1RE_0RF0RA_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1093: ~halts (TM_from_str "1RB0LC_0LC1RF_1LE1RD_0RC0LF_0LA1LA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1094: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD---_1LA1LF_0LD1RF_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1095: ~halts (TM_from_str "1RB0RE_1LC---_1RD1LB_0LE0LA_1RF1LD_0RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1096: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA0LD_0LE0RF_0RB1LD_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1097: ~halts (TM_from_str "1RB1LF_1LC1LD_1RD1LA_---0RE_0RC1RA_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1098: ~halts (TM_from_str "1RB0RD_1LC1RD_---0LD_1RA0LE_1RD0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1099: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1LE1LF_1RA1RE_0LE1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1100: ~halts (TM_from_str "1RB1LE_1LC0RA_1LE1RD_---0RB_0LA0LF_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1101: ~halts (TM_from_str "1RB0RB_1RC1RA_0RD1LE_1RE1RF_1LC0LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1102: ~halts (TM_from_str "1RB0RF_1RC---_1LD0LA_0RA0LE_1LC1LE_0LA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1103: ~halts (TM_from_str "1RB1RD_1LC1RE_1RE0LD_1LC1LB_---1RF_0RA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1104: ~halts (TM_from_str "1RB---_1LC0LF_1RF0RD_1RC0LE_1LB1RA_0RE0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1105: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1LA1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1106: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RE_0LA1LE_0RA0RF_0LD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1107: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LA0LF_0LB0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1108: ~halts (TM_from_str "1RB0RE_1LC1RD_1LD0LD_1LA1RF_---0LC_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1109: ~halts (TM_from_str "1RB1RF_1LC1RB_1LE0LD_1LB1LD_0RE0RA_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1110: ~halts (TM_from_str "1RB0RF_1RC---_1LD0LE_1RA0LC_1LC1LA_1RE0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1111: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0RF_0LC1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1112: ~halts (TM_from_str "1RB1LC_0LA1LD_1RD1RF_1LE0RC_---1LB_1RD1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1113: ~halts (TM_from_str "1RB1RE_0LC0RE_---1LD_1LE0LF_0RA1LD_1LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1114: ~halts (TM_from_str "1RB1LE_0RC1LA_1RD1RA_0LA1LF_1LB0LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1115: ~halts (TM_from_str "1RB0LE_1RC1LB_1LD0RF_---1LA_1LB1LD_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1116: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_1RE1LF_1RA1RE_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1117: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD0RB_0LE1LF_1RB1LC_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1118: ~halts (TM_from_str "1RB1LD_1RC0LE_0LA0RF_0LF1LE_0LB0RB_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1119: ~halts (TM_from_str "1RB1LA_1RC0LE_0RD0RE_0RE0RF_1LE0LA_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1120: ~halts (TM_from_str "1RB1LE_0RC1LF_1LD0RA_1LE0LB_0LA0LC_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1121: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0RA0RA_0LE0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1122: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_0LB0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1123: ~halts (TM_from_str "1RB0LD_0LC1RA_1LA1LD_0LC1RE_---0RF_1RC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1124: ~halts (TM_from_str "1RB0RD_1LC0RE_---1LD_1RE1LF_1RA1RE_1LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1125: ~halts (TM_from_str "1RB---_0RC1LF_1RD0RE_1LE0LF_1RC0LD_0LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1126: ~halts (TM_from_str "1RB1RF_1LC0RA_---1LD_0LE1LB_1RD1LA_1RB1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1127: ~halts (TM_from_str "1RB1RA_0LC---_1LE0RD_0LE1RC_1LF1LC_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1128: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1RA1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1129: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1LA1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1130: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1131: ~halts (TM_from_str "1RB1RF_1LC1RA_0LE0LD_1LC1RE_1LA0LB_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1132: ~halts (TM_from_str "1RB1LF_0RC0RA_1RD0RA_1LE---_1RF1LD_0LA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1133: ~halts (TM_from_str "1RB1RF_1LC1RB_1RE0LD_1LB1LD_---1RA_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1134: ~halts (TM_from_str "1RB1RC_1LC0RC_0RA1LD_1LB0LE_1LA0LF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1135: ~halts (TM_from_str "1RB1RD_0RC1RA_1LD1RB_0LE1RF_1LA0LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1136: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_0RF0LC_1LC0RA_0LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1137: ~halts (TM_from_str "1RB0LE_0RC---_1RD0RA_0RE1RA_1LD1LF_0LA0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1138: ~halts (TM_from_str "1RB0LB_1LC0RA_1RD0LB_0LA0RE_0RF---_1LD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1139: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1140: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA0LD_1LA0RA_1RC1RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1141: ~halts (TM_from_str "1RB1LE_1RC1LB_1LD1RF_---0LA_0LB1LD_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1142: ~halts (TM_from_str "1RB0LC_1LA0RD_1LA0LB_1RE---_1RC1RF_0LC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1143: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1LE0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1144: ~halts (TM_from_str "1RB1RF_1LC1RA_---0LD_0RE1LA_1RD1LF_0RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1145: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_1LD0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1146: ~halts (TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RA1LE_0LF0RD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1147: ~halts (TM_from_str "1RB1LF_0LC0LA_1LE0RD_1RC1RB_---0LF_1LD0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1148: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LB0LE_---1LF_0RF1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1149: ~halts (TM_from_str "1RB1LB_0RC0LA_1LA1RD_1RE0RF_1LF1RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1150: ~halts (TM_from_str "1RB0RC_0LC0RF_1LE0LD_0RC1LC_1LA---_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1151: ~halts (TM_from_str "1RB0RF_0RC0RA_1LD---_1LE0LB_1RB0RF_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1152: ~halts (TM_from_str "1RB1LF_1LC0LD_1RE1LA_---0RE_1RA0RA_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1153: ~halts (TM_from_str "1RB1LD_1LC0LF_1RA0LB_1RB1RE_---0RD_1LB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1154: ~halts (TM_from_str "1RB1RF_1LC1RD_---0LD_1LE0LA_1RF1RC_0RA1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1155: ~halts (TM_from_str "1RB1RD_1LC0RF_1LD1LC_1RA0LE_0RA1LD_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1156: ~halts (TM_from_str "1RB1RD_1LC0RA_1LA0LC_0LB0LE_---1LF_1LA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1157: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1158: ~halts (TM_from_str "1RB0RB_1RC1LC_0LD0RA_0LE1LB_1RC0LF_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1159: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RE0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1160: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_0RB0LB_1RF1LE_1LE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1161: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_0LA1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1162: ~halts (TM_from_str "1RB1LC_0LC1RD_1LA1LB_1RE0RF_---1RA_1RC1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1163: ~halts (TM_from_str "1RB1LF_0LC0LE_1RD1LB_0RE0RC_1RF0RC_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1164: ~halts (TM_from_str "1RB1RB_0RC1RF_1LD---_1LE0RF_0RA0LC_0RD0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1165: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---0RF_1LA1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1166: ~halts (TM_from_str "1RB0RC_1LC0LE_1RD0LB_1RF0RA_1LC0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1167: ~halts (TM_from_str "1RB1RA_1LC0RE_1RD0LB_1LF0RA_1LD1RB_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1168: ~halts (TM_from_str "1RB0LE_1LC---_1RD1RC_1LA0LF_0LF1LA_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1169: ~halts (TM_from_str "1RB0RD_0RC---_0RD1LE_1LE1RC_1LC0LF_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1170: ~halts (TM_from_str "1RB---_1LC0RF_1LF0LD_1LE0LA_0LB0LE_1RB0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1171: ~halts (TM_from_str "1RB---_1RC0LE_1RD0RB_0RE0RC_1LF0RA_1LC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1172: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_1LE0RB_1LC1LF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1173: ~halts (TM_from_str "1RB0LC_1LA1RE_1LD0LF_1RB0RE_1LD1RB_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1174: ~halts (TM_from_str "1RB0LD_1RC0LF_1LC0RA_1LE---_0LA1LF_0LB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1175: ~halts (TM_from_str "1RB0RF_0RC0RE_1LD---_1LE0LB_1RB0RF_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1176: ~halts (TM_from_str "1RB1RF_1LC---_1RA0LD_1LE0LE_0RA1LF_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1177: ~halts (TM_from_str "1RB0RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1178: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1RC0LB_1RC---_1LC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1179: ~halts (TM_from_str "1RB0RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1180: ~halts (TM_from_str "1RB0RF_1LC0LD_1LD0LD_1LA1RE_1RD0RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1181: ~halts (TM_from_str "1RB1LA_0LC0RE_1RA0LD_0LE0LF_1RC1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1182: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_0RE0LB_---1LA_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1183: ~halts (TM_from_str "1RB1RE_1LC1RA_---0LD_1LA1LA_0RB0LF_1RE1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1184: ~halts (TM_from_str "1RB0LC_0LC0RD_1LD1LA_1RE0RF_1LF1RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1185: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD1LF_1LA1RC_1RA0LC_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1186: ~halts (TM_from_str "1RB1RC_1LC0LD_0RA1LB_1LE1LF_1RF0RC_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1187: ~halts (TM_from_str "1RB0RF_0RC0RA_1LD1LE_1RC0LB_---1LA_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1188: ~halts (TM_from_str "1RB0RC_0LC1LB_1RE0LD_1LB0RC_0RF---_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1189: ~halts (TM_from_str "1RB1LC_0LC0LD_1RD1LB_0RE0RC_1LF0RF_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1190: ~halts (TM_from_str "1RB1RE_1LC0LF_1RD0LD_0LE0RE_1LB1RA_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1191: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1192: ~halts (TM_from_str "1RB1LA_0LC1RE_1RF0LD_1LA1LC_0RA1RC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1193: ~halts (TM_from_str "1RB0LF_1LC1RE_1LA1LD_1LC0RF_---1RB_0LC1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1194: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD0RA_0LA0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1195: ~halts (TM_from_str "1RB1LF_0RC1LE_1LD0RA_0LE1LA_---1RC_0LA1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1196: ~halts (TM_from_str "1RB1LD_1LC0RF_---0LD_0LE1LB_1LA1RF_1RE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1197: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD0RA_1LB0LE_---1LF_0RF1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1198: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA0LD_1LA0RA_1RC0RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1199: ~halts (TM_from_str "1RB1RC_1LC0RA_0RB0LD_1LA1LE_1LA1LF_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1200: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA0LF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1201: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_---0LE_1LB1LA_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1202: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RA_1LE1LF_0LA1LD_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1203: ~halts (TM_from_str "1RB0RD_1LC---_1LD1LB_1RE1LF_0RA0RD_0LD0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1204: ~halts (TM_from_str "1RB0LF_0LC0RC_1RA1LD_0LE1LF_1RA---_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1205: ~halts (TM_from_str "1RB1RA_0RC0RF_1LC0LD_1LE1LD_1LA---_0LC0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1206: ~halts (TM_from_str "1RB1RE_1LC1RD_1RB0LD_1RA0LE_0RC0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1207: ~halts (TM_from_str "1RB0LC_1RC1RF_0RD1LE_1LE1RC_1LA0LD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1208: ~halts (TM_from_str "1RB---_1LC1LD_0LD1LB_1RE0LB_1RF1RD_0RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1209: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RF_1RE0LB_---0LA_1RC1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1210: ~halts (TM_from_str "1RB1LB_1LC0LE_1RD0LB_0LF0RA_1LD0RC_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1211: ~halts (TM_from_str "1RB0LD_1RC1LB_0LA0RF_---1LE_1LB1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1212: ~halts (TM_from_str "1RB1RF_1LC1RB_0RE0LD_1LB1LD_---0RA_0RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1213: ~halts (TM_from_str "1RB0LC_1LA1LD_0RB0RE_---1LE_1RC0RF_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1214: ~halts (TM_from_str "1RB---_0LC0RD_0LE0LD_1LC1RE_1RA0LF_1LB1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1215: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_1LE1LF_1RB0RA_1RF1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1216: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0RE0LE_---1LF_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1217: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_0LF1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1218: ~halts (TM_from_str "1RB1RC_1LC0RE_1RA0LD_0LB1LB_0RC0RF_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1219: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1RE0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1220: ~halts (TM_from_str "1RB0RE_1LC---_1LD1LC_1RA0RF_0RF1RA_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1221: ~halts (TM_from_str "1RB0LD_1LC0RE_---0LD_1LA0LF_1RF0RD_1LD1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1222: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RB0LE_---1LF_0LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1223: ~halts (TM_from_str "1RB---_0RC0RE_1LD1RB_0LE0LC_1RF0LC_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1224: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD0RA_1LB0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1225: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA0RB_1RE0RF_1LF1RD_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1226: ~halts (TM_from_str "1RB---_1RC0LF_0LD0RA_---1LE_0LA1LF_0LB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1227: ~halts (TM_from_str "1RB0RC_1LC0LF_0LD1RD_1RA1LE_---0LB_1LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1228: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LE0LB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1229: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0LE0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1230: ~halts (TM_from_str "1RB0RC_1LC0LF_0RD0LB_0LE1LD_1RA---_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1231: ~halts (TM_from_str "1RB0LB_0RC0LD_1LA1RE_1RB1LB_1RC0RF_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1232: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1233: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD0RA_1LE0RB_1LC1LF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1234: ~halts (TM_from_str "1RB0LA_0LC0LD_1RD1LB_0RE0RC_1LF0RF_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1235: ~halts (TM_from_str "1RB1LC_1LC0RF_---1LD_0LE1LB_1LF1LF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1236: ~halts (TM_from_str "1RB0RF_1LC1RA_---0LD_1RE1LA_1LD0RA_0RC0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1237: ~halts (TM_from_str "1RB0LD_1RC0RF_0RD0RA_1LE1RC_0LA0LD_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1238: ~halts (TM_from_str "1RB0LB_1LC1RD_1RE0LD_1RA0LC_0RF0RA_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1239: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_0RD0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1240: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1241: ~halts (TM_from_str "1RB1LE_1RC0RF_1LD0RD_0RA0LA_1LB1LA_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1242: ~halts (TM_from_str "1RB1RE_1LC0RF_---1LD_1LE1LC_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1243: ~halts (TM_from_str "1RB1RE_1LC1LB_1LD1RC_1RA0LB_0RB1RF_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1244: ~halts (TM_from_str "1RB1RA_0LC---_0LE1RD_1LE0RC_1LF1LD_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1245: ~halts (TM_from_str "1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1RC0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1246: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD1RB_0LE0LC_1LA0LC_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1247: ~halts (TM_from_str "1RB1LF_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1248: ~halts (TM_from_str "1RB1RE_1LC1RB_0RB1LD_1LC1LE_1LF0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1249: ~halts (TM_from_str "1RB0RF_1LC0RD_1LD0LC_1RE0LC_1RA0RE_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1250: ~halts (TM_from_str "1RB0LF_1LC0LD_0RD1LB_0RE1RD_1RA0RF_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1251: ~halts (TM_from_str "1RB1RC_0LC1LF_1RE1LD_1LE0LB_0RA1LC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1252: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_0LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1253: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_---0RF_0LC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1254: ~halts (TM_from_str "1RB0RC_0LC0RF_1LE0LD_1RC1LB_---1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1255: ~halts (TM_from_str "1RB1LD_1LC0RA_0LE0LD_0LE1LE_1RF1LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1256: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RE_1RB1RF_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1257: ~halts (TM_from_str "1RB0RF_1RC---_1LD0LA_0RA0LE_1LC1LE_0LF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1258: ~halts (TM_from_str "1RB0RA_0LC0LE_0RD1LB_1RA---_0LF0RB_1LC1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1259: ~halts (TM_from_str "1RB0RE_1LC0RA_1LA0LD_1LA1RA_1RF0LB_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1260: ~halts (TM_from_str "1RB1RF_1LC---_1RF0LD_1LE1LC_0RA1LE_0RA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1261: ~halts (TM_from_str "1RB1RC_1LC0RE_1RA0LD_0LB1LB_0RF0LB_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1262: ~halts (TM_from_str "1RB1RF_1LC0LE_1RE0LD_1LB1LD_---1RA_1RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1263: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1RA0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1264: ~halts (TM_from_str "1RB1RF_0RC1RC_1LD0LA_0LE---_1LF1LE_0RB1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1265: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LE0LF_1RB0RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1266: ~halts (TM_from_str "1RB0RC_1LC1RE_---0LD_1LA1RB_0RF1RA_1RF1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1267: ~halts (TM_from_str "1RB1RC_1LC0RE_1RA0LD_0LB1LB_0RC0RF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1268: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA1RD_1LD0RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1269: ~halts (TM_from_str "1RB1LD_1LC0RC_1RD1RC_0LE1LA_1RB1LF_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1270: ~halts (TM_from_str "1RB0RA_1LC1LF_1RA0RD_0LC1LE_0LB---_1LD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1271: ~halts (TM_from_str "1RB1RE_1LC1RB_0RE1LD_0LB1LE_1LF0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1272: ~halts (TM_from_str "1RB---_0RC1RD_1LD1LF_1LE0RB_1LF1LD_1LA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1273: ~halts (TM_from_str "1RB0LB_1RC---_1LD1RF_0RF0RE_0LA0LF_1LE1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1274: ~halts (TM_from_str "1RB1LB_1LC1RF_1RE1RD_---0LA_1LE0LB_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1275: ~halts (TM_from_str "1RB0LD_0RC0RC_1RD0RF_1LA1LE_0RA0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1276: ~halts (TM_from_str "1RB0LD_0LC1RA_---1LA_1LF1RE_0RD0RC_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1277: ~halts (TM_from_str "1RB---_1RC0RB_1LC0LD_0LC0LE_1RF1RC_0RE1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1278: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_1LA1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1279: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_1RF0LC_1LD0RA_0RE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1280: ~halts (TM_from_str "1RB1LC_1RC0RA_0LD1LD_1RF1LE_0LD0LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1281: ~halts (TM_from_str "1RB1LD_1RC0LA_0RD1RF_1LE0RB_0LB0LA_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1282: ~halts (TM_from_str "1RB1LC_0RC0RC_1LD0RE_1LA1LE_0LD0RF_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1283: ~halts (TM_from_str "1RB1RF_1LC0RE_---1LD_0LE1LC_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1284: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LB1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1285: ~halts (TM_from_str "1RB0RD_1LC1LF_1LD0LB_1RA0RE_1RA0LA_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1286: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_---0LE_1LA1LF_0LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1287: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE1LF_1RD0LC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1288: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0LA0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1289: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_---1LB_1LF0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1290: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RB0LE_---1LF_0RF1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1291: ~halts (TM_from_str "1RB1LF_1LC0RD_0LD1RC_---0RE_1RF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1292: ~halts (TM_from_str "1RB1LE_0RC0LE_1LD0RF_0RA0LE_0LA1RD_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1293: ~halts (TM_from_str "1RB1LA_1RC0RF_1RD1RF_1LE0LA_---0LD_0LA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1294: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0LF0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1295: ~halts (TM_from_str "1RB0LD_0RC0RE_0LD1RA_1LA0LB_1RF---_1RD1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1296: ~halts (TM_from_str "1RB1RF_1LC0RA_---1LD_0LE1LB_1LA0RD_1RB1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1297: ~halts (TM_from_str "1RB0LC_1LC1RE_1LD1LC_1LA0LB_1RD1RF_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1298: ~halts (TM_from_str "1RB1LC_1RC0LF_0LA0RD_1RA1RE_1LF1RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1299: ~halts (TM_from_str "1RB0RB_0LC0RE_1RA1LD_1LC0LF_1LB1RB_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1300: ~halts (TM_from_str "1RB1RA_0LC0RA_1LE0LD_1RC1LB_---1LF_1RB1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1301: ~halts (TM_from_str "1RB0LC_1RC1LB_0RD0LF_0RE1RE_1LA1RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1302: ~halts (TM_from_str "1RB---_1RC1RD_1RD0RE_1LE0LF_1LA0LD_1LD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1303: ~halts (TM_from_str "1RB---_0RC1RE_1LD0RD_0LE0LF_0RA0LF_0LC0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1304: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_1RF0LC_1LD0RA_1RE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1305: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA0LF_1RB0LC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1306: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1LB0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1307: ~halts (TM_from_str "1RB0LC_1LA0RE_1LD---_1LE1LF_1RB0RA_0RE1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1308: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1309: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1RA0LC_1RA---_1LA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1310: ~halts (TM_from_str "1RB0LF_1LC0RE_---0LD_1LE0RB_1LF1RA_0RA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1311: ~halts (TM_from_str "1RB0RE_1LC0RA_1RD0LD_1LA0LF_1RB1LC_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1312: ~halts (TM_from_str "1RB1RD_0LC1RE_1LD1LB_1RA0LB_---0RF_1RC1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1313: ~halts (TM_from_str "1RB0RE_1LC0RA_1LF0LD_1LA---_1RB0LC_1LA0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1314: ~halts (TM_from_str "1RB---_1RC1RA_1RD1LE_1LE0LF_1RB0LD_1LE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1315: ~halts (TM_from_str "1RB1RE_0RC1RA_1LD1RB_0LE0LC_1LF0LC_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1316: ~halts (TM_from_str "1RB1LD_1RC1LB_1LD0RF_---0LE_1RF1LA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1317: ~halts (TM_from_str "1RB1LD_1LC0RA_0LA0LD_1LE---_1RF1LB_0RC0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1318: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD_------") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1319: ~halts (TM_from_str "1RB1LD_0RC0LE_1RD0RE_0LA0LF_1RC---_0LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1320: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_0LD0LD_0RE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1321: ~halts (TM_from_str "1RB0RA_1RC0RF_1LD0RE_1LE0LD_1RA0LD_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1322: ~halts (TM_from_str "1RB1LC_1LA0RE_1RD1LE_1LA0LB_1LD0RF_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1323: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_0LB0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1324: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1325: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1LF0LC_1RA---_0RD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1326: ~halts (TM_from_str "1RB0LC_1LA0RD_0RA0LE_1RA0RF_1LC0LE_1RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1327: ~halts (TM_from_str "1RB1LE_1LC0RA_1LE0LD_0RB---_0LF0LB_1RD1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1328: ~halts (TM_from_str "1RB0RC_1LC1RF_1RD0LB_1RA1LE_---0LC_0RB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1329: ~halts (TM_from_str "1RB0RC_1LC0RA_0LF0LD_1LE---_1LA1LF_0RA1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1330: ~halts (TM_from_str "1RB1LC_1RC1RE_1LA0LD_1LC1RF_---0RC_0RD1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1331: ~halts (TM_from_str "1RB0RD_0LC1RA_1LA1LB_1RE1LB_1LF1LB_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1332: ~halts (TM_from_str "1RB0LD_1RC1RA_1RD1LC_1LE1LA_0RF1LC_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1333: ~halts (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA1RC_0RD0RF_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1334: ~halts (TM_from_str "1RB1LA_1LC0RC_1LE1RD_0LA1RC_1LE1LF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1335: ~halts (TM_from_str "1RB0LB_0RC1LD_0LD1RA_1LA1RE_0RF1RC_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1336: ~halts (TM_from_str "1RB0RE_0LC0RD_0LD1LC_1RA0LA_1RF1LD_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1337: ~halts (TM_from_str "1RB1LD_1LC1LE_1RE0RA_1LA0LB_---0RF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1338: ~halts (TM_from_str "1RB0RB_1LB0LC_1RD1LC_1RE0RF_1RB1RA_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1339: ~halts (TM_from_str "1RB1RD_1LC1LD_1RE0LD_0LB1RF_0RB1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1340: ~halts (TM_from_str "1RB0RB_1LC0LD_1RD1RC_1LE0LF_---1LA_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1341: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_1RD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1342: ~halts (TM_from_str "1RB0LD_0RC0RE_0LD---_1LA0LF_1RF0RD_1LD1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1343: ~halts (TM_from_str "1RB0RE_1LC0RA_---0LD_1LA0LB_1RB0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1344: ~halts (TM_from_str "1RB0RC_1LC0LE_0LD0LB_1RA---_1RF0RD_0LF1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1345: ~halts (TM_from_str "1RB1RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1346: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0LF0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1347: ~halts (TM_from_str "1RB1LF_1RC1RF_1RD1LC_1LD0LE_---1LA_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1348: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RF_1LE0RA_1LF1LE_1RC0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1349: ~halts (TM_from_str "1RB0LF_0LC0RE_1LD0RB_0LE1LF_1RA---_0LA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1350: ~halts (TM_from_str "1RB0RD_1LC0LE_1RA0LB_1RB1RF_1LB0RC_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1351: ~halts (TM_from_str "1RB1LA_1LC0RC_---1RD_0RF0RE_1LE0LA_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1352: ~halts (TM_from_str "1RB---_1LC0RE_1LD0LB_0LE0LC_1RF1LA_1RC0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1353: ~halts (TM_from_str "1RB0LF_1LC0RE_---0LD_1LE0LB_1RB0RA_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1354: ~halts (TM_from_str "1RB0RE_1LC0LF_1RE0LD_1LB1LD_1RB1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1355: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD1RE_1LD0LA_0LF0RD_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1356: ~halts (TM_from_str "1RB0LB_1LA1LC_1LA1RD_0RF1RE_0RF1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1357: ~halts (TM_from_str "1RB0LA_1RC---_1RD0LA_1LE0RF_0LF0LE_1LC0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1358: ~halts (TM_from_str "1RB0LB_0RC0RC_1LD0RF_1LE0LE_1LA1RC_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1359: ~halts (TM_from_str "1RB0RE_1RC0RA_1RD1LC_1LE1RD_---0LF_1LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1360: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_1RF---_0LB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1361: ~halts (TM_from_str "1RB0LB_1LC1LF_1RE0RD_1RE0LE_1LA0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1362: ~halts (TM_from_str "1RB0RC_1LC0LE_1RA0LD_1RC0LB_1LF0RD_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1363: ~halts (TM_from_str "1RB1LC_1LC0RF_---1LD_0LE1LB_1RD1LF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1364: ~halts (TM_from_str "1RB1RE_1LB0LC_1RD1LC_1RA0RE_0LF0RB_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1365: ~halts (TM_from_str "1RB1LC_1LC0RF_---1LD_0LE1LB_1LA1LF_1RB1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1366: ~halts (TM_from_str "1RB1LD_1LC0RA_0RA0LD_0LE1LE_1RF1LC_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1367: ~halts (TM_from_str "1RB1RF_1LC1LB_1LD1RC_1RE0LB_1RB0RA_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1368: ~halts (TM_from_str "1RB1RA_0RC0RA_0LD1LE_0LC---_1LF0LF_1RB0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1369: ~halts (TM_from_str "1RB0LE_0RC1RE_1LD1RA_0LA---_0LC0LF_0RB1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1370: ~halts (TM_from_str "1RB0LD_1LC0RE_---1LD_1LA1LB_1RD1RF_1RD0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1371: ~halts (TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_1LF---_0RD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1372: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_0RB1LD_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1373: ~halts (TM_from_str "1RB0LF_0LC0RD_1LE1RD_0RC1LE_0LA0LC_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1374: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1LC0LB_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1375: ~halts (TM_from_str "1RB0RC_0RC1RC_1LD0RB_1LE0LF_0LA1LC_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1376: ~halts (TM_from_str "1RB0RC_1LA0RE_1LC0LD_1LB1LD_---0RF_0RC1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1377: ~halts (TM_from_str "1RB1LC_1RC1RB_1RD0LF_1RE1LD_0LA0RB_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1378: ~halts (TM_from_str "1RB0LE_0RC0RF_1LD1RF_0LA0LC_1LA---_0RC1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1379: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD0LD_1LE0LF_1RB0RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1380: ~halts (TM_from_str "1RB0LF_0RC0RD_1LA0LE_1RE0RC_1LC1LB_1LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1381: ~halts (TM_from_str "1RB1LE_0RC1LA_1RD1RA_0LA0LF_1LB0LD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1382: ~halts (TM_from_str "1RB0LD_0LC1RA_---1LA_1LF1RE_0RD0RC_0LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1383: ~halts (TM_from_str "1RB1RF_1LC0RA_---0LD_0LE0LB_1LF1LD_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1384: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LF0LB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1385: ~halts (TM_from_str "1RB0LE_0RC1RD_1LA1RB_1RC1LE_0LC0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1386: ~halts (TM_from_str "1RB1RA_1RC1LB_0RD1RE_1LD0LB_0RA0RF_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1387: ~halts (TM_from_str "1RB1RD_0RC1LE_1LC0LA_1LB1LF_0LC1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1388: ~halts (TM_from_str "1RB1LF_1RC0LA_1RD1RC_1RE1LD_0LB0RC_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1389: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RB0LF_1RC1RF_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1390: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_---1LF_0RF1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1391: ~halts (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA0LF_0LC1RB_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1392: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LC0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1393: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_0LC0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1394: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RE_1LF0LB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1395: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD0RE_0LA1LC_1RC1LD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1396: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD1RE_0LA1LA_0RC1RB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1397: ~halts (TM_from_str "1RB1RC_1LC0RA_0LB0LD_1LA1LE_1LA0LF_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1398: ~halts (TM_from_str "1RB0LB_0RC0LD_1LA1RE_1RB1LB_1RC0RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1399: ~halts (TM_from_str "1RB0LE_1RC0RA_0LD0RB_0RE1RD_1LF---_1LB0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1400: ~halts (TM_from_str "1RB0RE_1LC1LB_1LD1RC_1RA0LB_1LB1RF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1401: ~halts (TM_from_str "1RB0RB_1LC1RE_---0LD_1RE0LF_1RB0RA_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1402: ~halts (TM_from_str "1RB1RF_1RC1LB_0LC0LD_---1LE_0RE1LF_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1403: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1LF0LD_0RE0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1404: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD0LA_0LF1RA_0RC1RE_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1405: ~halts (TM_from_str "1RB1RE_1LC1LE_0RD1LB_1LC1RD_1LF0RA_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1406: ~halts (TM_from_str "1RB1LA_0LC1RE_1RF0LD_1LA1LC_0RA1RC_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1407: ~halts (TM_from_str "1RB1LF_0RC0LE_1LD0RD_1RE1RD_0LA1LE_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1408: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_1RD0LB_1LC0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1409: ~halts (TM_from_str "1RB---_1LC0RE_1LA0LD_1LB1RE_1RD0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1410: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1RC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1411: ~halts (TM_from_str "1RB0RB_0LC0RE_1RA1LD_1LC1LF_1LB1RB_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1412: ~halts (TM_from_str "1RB1RF_1LC0LE_1RA0LD_1LE0LB_0RD0RF_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1413: ~halts (TM_from_str "1RB1LD_1RC0RC_0RD1RA_1RE0LA_1LA1LF_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1414: ~halts (TM_from_str "1RB1RD_0LC1RA_1RB1LC_1RF0LE_1RB1LD_---0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1415: ~halts (TM_from_str "1RB0RB_1RC0LD_1RD1RC_1LE0LF_---1LA_1RF0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1416: ~halts (TM_from_str "1RB0RB_0RC1RA_1LC0LD_1LE1LD_1RA0LF_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1417: ~halts (TM_from_str "1RB1LE_0RC1RB_1LD1RD_0LA0LB_1LA1LF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1418: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RB0LE_---1LF_1RB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1419: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA1RF_1LA0LB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1420: ~halts (TM_from_str "1RB---_1RC1RF_1LD0RE_0LA1LD_0RB1LF_1RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1421: ~halts (TM_from_str "1RB0LB_1LC1RF_1LE0LD_1LE0RE_1RD0RA_0LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1422: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_1LE0LE_0LA1RB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1423: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_0LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1424: ~halts (TM_from_str "1RB1RD_1LC0LE_1RA0LB_1RA1LE_1LF0RD_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1425: ~halts (TM_from_str "1RB1LE_0RC0RA_1LD0RF_0LA0LE_0LA1RB_1RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1426: ~halts (TM_from_str "1RB0RE_1LC1RE_1RB0LD_1LA0LF_1LA1RB_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1427: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RB_0LE0LC_1LA0LC_1RB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1428: ~halts (TM_from_str "1RB0RB_1LC1RE_1RA0LD_1LA1LD_1RF1RB_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1429: ~halts (TM_from_str "1RB1RF_1RC1LD_1LD0LE_---0LC_1LF0RA_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1430: ~halts (TM_from_str "1RB1RA_1LC0RE_1LD1LB_1RA0LE_0LC0LF_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1431: ~halts (TM_from_str "1RB1RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1432: ~halts (TM_from_str "1RB1LA_0LC0RE_0RC0LD_1RE1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1433: ~halts (TM_from_str "1RB1LE_0RC0RA_1RD0RA_1LE1LF_0LA1LD_---0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1434: ~halts (TM_from_str "1RB0LC_0RC1RF_1LD1RE_0LA1LA_0LE1RB_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1435: ~halts (TM_from_str "1RB1RF_1LC0RA_---0LD_0LE0LB_1LF1LD_1RA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1436: ~halts (TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LE_0RA0RF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1437: ~halts (TM_from_str "1RB0RF_0RC0LD_1LD0RA_1LE0LC_1RC1RB_0RD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1438: ~halts (TM_from_str "1RB0RF_1RC1LB_1LD0RA_1RA1LE_---0LF_0LD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1439: ~halts (TM_from_str "1RB0LD_0LC1RA_---1LA_1LF1RE_0RD1RF_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1440: ~halts (TM_from_str "1RB1LE_1LC0LA_---1LD_1RE1LD_0LB0RF_1RE1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1441: ~halts (TM_from_str "1RB1LF_1RC0RA_1LD0RF_---1LE_1RB0LB_0LA0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1442: ~halts (TM_from_str "1RB1LE_1LC0LD_1RD1LA_1LC0RE_1LB0RF_---1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1443: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1LE0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1444: ~halts (TM_from_str "1RB0RE_1LC0RA_1LD0LD_1LA0LF_1RB0LC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1445: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0LE_0RE1RD_1LF0LA_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1446: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD0RE_0LA1LC_1RC0LB_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1447: ~halts (TM_from_str "1RB0RF_1RC0LF_1LD0LE_0RE1LC_0RA1RE_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1448: ~halts (TM_from_str "1RB1LA_1LC1RE_---1LD_1RA0LE_0RF0LB_1RD1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1449: ~halts (TM_from_str "1RB1RF_1LC1RB_0RE0LD_1LB1LD_---0RA_1LB1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1450: ~halts (TM_from_str "1RB1RC_0LC0LF_1RE1LD_1LE0LB_0RA1LC_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1451: ~halts (TM_from_str "1RB1RF_0RC0RE_1LD1RB_0LE0LC_1RA0LC_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1452: ~halts (TM_from_str "1RB0RC_1LC0LE_1RD0LB_0RF0RA_1LC0RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1453: ~halts (TM_from_str "1RB1RA_1LC0LE_---1LD_1LE0LB_1RF1LE_1RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1454: ~halts (TM_from_str "1RB1RE_1LC0LF_1RA0LD_1RE0LB_1RC---_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1455: ~halts (TM_from_str "1RB1LD_1LC0LE_1RF0RA_1LA0LB_---0RF_1RA0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1456: ~halts (TM_from_str "1RB---_1RC---_1RD0RE_1LE0LF_0LB0LD_1LD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1457: ~halts (TM_from_str "1RB1RF_1LC0RE_---1LD_1RE1LC_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1458: ~halts (TM_from_str "1RB1LD_0RC0RE_1RD0LA_0LA1LA_---0RF_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1459: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1460: ~halts (TM_from_str "1RB---_1LC---_1LE0LD_0RB0RE_1RD0RF_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1461: ~halts (TM_from_str "1RB0LB_1LA0LC_1LD0RD_1RE1LF_1RB0RA_0RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1462: ~halts (TM_from_str "1RB1RF_1LC0LE_1RD0LB_1LA0RA_1LB0RC_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1463: ~halts (TM_from_str "1RB0LC_1LA0RE_0LD---_1LB1LD_1RF1RF_0RD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1464: ~halts (TM_from_str "1RB1RE_1LC0RF_0RA0LD_1LB---_0RD1RF_0RB0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1465: ~halts (TM_from_str "1RB1RF_0RC0RA_1RD---_1LE1LF_1RF1LD_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1466: ~halts (TM_from_str "1RB1RD_1LC0RD_1LA1LB_0RA1LE_1LF0LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1467: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_0RE0LA_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1468: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA1LE_---0LF_0LD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1469: ~halts (TM_from_str "1RB0RE_0LB0LC_1LD1LF_1RA1LD_1RD1RE_---1LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1470: ~halts (TM_from_str "1RB0RF_1LC---_1RA0LD_1LE1RD_1LF0LA_1RA0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1471: ~halts (TM_from_str "1RB0RC_1LC0LD_---0LD_0LE1RF_1RF1LD_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1472: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0RF_1RA0LC_0LB1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1473: ~halts (TM_from_str "1RB0LE_1RC0RA_1RD1LC_1LA0RB_1RA1LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1474: ~halts (TM_from_str "1RB0RF_1RC0RA_0LC0RD_1LE---_1LA0LB_1RA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1475: ~halts (TM_from_str "1RB0RA_1LC0LD_1RA0LB_0LE0RC_1LB1LF_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1476: ~halts (TM_from_str "1RB1RD_0RC1RB_1LD0RA_0LE---_1LB1LF_0RF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1477: ~halts (TM_from_str "1RB1LA_1RC0RC_1LD1RF_1LD1LE_---0LA_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1478: ~halts (TM_from_str "1RB0LC_1RC1LB_1RD0RE_1RE0LF_1LD1RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1479: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD1RB_0LE0LC_1LA0LC_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1480: ~halts (TM_from_str "1RB---_1RC0RA_0LD0LE_1RF1LC_0LF0LB_0RB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1481: ~halts (TM_from_str "1RB0LE_1LC0RA_0LD1LB_1RE0LE_0RB0LF_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1482: ~halts (TM_from_str "1RB0LD_1RC0LA_1RD1RF_1LB0LE_1LB0RF_1RB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1483: ~halts (TM_from_str "1RB1LA_0LC0RE_1LA0LD_1RE1LF_1RA1RE_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1484: ~halts (TM_from_str "1RB1RA_1LC0RF_1LD1LB_1LE0LF_0RA---_0LC0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1485: ~halts (TM_from_str "1RB0RB_0RC1RF_1LD0LE_0LE1LE_1RA0LD_---1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1486: ~halts (TM_from_str "1RB0LD_1LC0RF_1LE1LD_1LB---_1RB0RA_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1487: ~halts (TM_from_str "1RB0LD_0RC1RC_1LA1RD_0RC0LE_---0LF_1RA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1488: ~halts (TM_from_str "1RB1RF_1LB0LC_0LD1RE_1RE1LC_1RC0RA_---0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1489: ~halts (TM_from_str "1RB0RE_1LC0RD_1LF1LD_1RA0LC_0RB1LD_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1490: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1RD0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1491: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_0LF0LC_1LC0RA_1RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1492: ~halts (TM_from_str "1RB1RC_1LC1LD_1RA0LD_0LB1RE_---0RF_1RB1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1493: ~halts (TM_from_str "1RB1RE_1LC0RA_---0LD_1LA1LF_0LB0LD_1LA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1494: ~halts (TM_from_str "1RB1LC_1RC0RD_1LD1RB_0RE1RE_1LF0LA_0LC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1495: ~halts (TM_from_str "1RB1RE_1LC0LE_1RD0LB_1RB0RA_0RF0RC_0LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1496: ~halts (TM_from_str "1RB0LB_1LA1LC_1LA1RD_0LD1RE_0RF1RA_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1497: ~halts (TM_from_str "1RB---_1RC0RA_1RD0LE_1LC0RB_0RC0LF_1LE0LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1498: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1LB0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1499: ~halts (TM_from_str "1RB---_0RC0RE_1LD1RB_0LE0LC_0LF0LC_1RF0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1500: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1501: ~halts (TM_from_str "1RB0RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1502: ~halts (TM_from_str "1RB0RE_0LC1RA_1RD1LB_0LB---_0RF1RF_1LD0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1503: ~halts (TM_from_str "1RB1RC_1LC1RD_0RA0LD_1RA0LE_0RA0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1504: ~halts (TM_from_str "1RB1RF_1LC1LF_0RE0RD_---1LE_1LB1RC_1RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1505: ~halts (TM_from_str "1RB1RE_1LC1RA_---0LD_0RE1LA_0RB0LF_1RE1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1506: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA1LD_1LB---_0RA0RA_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1507: ~halts (TM_from_str "1RB---_1RC0LE_0RD1RA_1LE1RB_0LB0LF_1LE0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1508: ~halts (TM_from_str "1RB1LA_1RC0LE_0RD1RB_1LE0RF_0LA1LB_0RC---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1509: ~halts (TM_from_str "1RB0RE_1LC---_1LF1LD_1RE0LC_1RA1RD_0LD1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1510: ~halts (TM_from_str "1RB0RD_0RC---_1RD0RA_1LE1RD_1LC0LF_0LA1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1511: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LB_1RA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1512: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0RF_1LA0LE_0LF---_0RB1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1513: ~halts (TM_from_str "1RB0LF_1RC1RB_1LD---_1LA1LE_1LD0RF_0LD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1514: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RD_0LA0RF_1LA0LB_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1515: ~halts (TM_from_str "1RB0RC_1RC0RC_1RD1LE_1LA0LF_1LC0LD_---0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1516: ~halts (TM_from_str "1RB1RF_1LB0LC_1RC1LD_1LB0RE_---1RA_0LC1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1517: ~halts (TM_from_str "1RB1LC_0LC---_0LA1RD_1RC0RE_0RF1RF_1LB0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1518: ~halts (TM_from_str "1RB0RC_1LC1RA_1RF1RD_---0LE_1LC1LB_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1519: ~halts (TM_from_str "1RB0LF_1RC1RB_1LD0RE_1LA1LC_0LD1RC_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1520: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD0RB_1LE---_1LB0LF_0RD0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1521: ~halts (TM_from_str "1RB0LF_0RC0LD_1LA1RE_1RB1LB_1RC1RF_---0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1522: ~halts (TM_from_str "1RB0LF_1LC0RF_1LE0LD_1LC---_1RB0RA_1LB0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1523: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_0LB1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1524: ~halts (TM_from_str "1RB1LC_1RC0RD_0LA1RB_1RE0RF_1LE0LC_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1525: ~halts (TM_from_str "1RB0RF_1LC0LE_1RD0LB_1RB0RA_1LB0RC_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1526: ~halts (TM_from_str "1RB1RE_1LC0RF_1LD1LC_1RA---_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1527: ~halts (TM_from_str "1RB---_1LC0RE_1LA0LD_1LC0LB_1RF1LE_1RD0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1528: ~halts (TM_from_str "1RB0LF_1RC1LE_0RD1RE_1LA1RC_1RD1LF_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1529: ~halts (TM_from_str "1RB0RF_0LC---_1LD1LC_1RE0LF_1RA1RD_0RE0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1530: ~halts (TM_from_str "1RB1RA_1RC0RF_0LD0RA_1LB0LE_---1LF_0RF1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1531: ~halts (TM_from_str "1RB1RF_1LC0LE_1RE0LD_1LB1LD_---1RA_1LD0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1532: ~halts (TM_from_str "1RB1LE_1RC0RD_1LD0LD_0RE0RA_0LC1RF_1RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1533: ~halts (TM_from_str "1RB0LC_0RC1RA_1LD1RB_0LE0LC_1RA1LF_0RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1534: ~halts (TM_from_str "1RB0RD_0LC1RA_1RA1LB_1RE0RF_1LF1RB_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1535: ~halts (TM_from_str "1RB1LA_0LC0RF_1LE0LD_1RC1LB_---1RA_1RB1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1536: ~halts (TM_from_str "1RB1RF_1RC1LB_1LC0LD_---1LE_1RA1LF_1RA0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1537: ~halts (TM_from_str "1RB1LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_1LB---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1538: ~halts (TM_from_str "1RB0LD_0LC1LD_---1RD_1LA1RE_0LB1RF_0RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1539: ~halts (TM_from_str "1RB0LC_1LC0RE_1LD1LC_1LA1RD_1LC1RF_---1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1540: ~halts (TM_from_str "1RB0LC_1RC1RE_1LA0LD_1LA0RA_1RB1RF_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1541: ~halts (TM_from_str "1RB1RE_1LC0RD_0LD1LC_0RA1LE_1RA0RF_---1LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1542: ~halts (TM_from_str "1RB1LF_1LC0RD_0LD1RC_---0RE_1LF1RB_0LA1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1543: ~halts (TM_from_str "1RB0LB_0RC0LF_1LD0RE_0LA1LC_1RC0RD_---1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1544: ~halts (TM_from_str "1RB1RD_0RC1RA_1LD1RB_0LE1RF_0RA0LC_---1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1545: ~halts (TM_from_str "1RB1LD_1LC1LE_1RE0RA_1LA0LB_---0RF_0RF1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1546: ~halts (TM_from_str "1RB0LE_1RC---_1RD0RF_1LA0RC_1LF0LC_1RC1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1547: ~halts (TM_from_str "1RB0LE_1RC1RF_1RD1LC_1LA0RF_---0LD_1LD1RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1548: ~halts (TM_from_str "1RB---_1RC0LF_0RD1RA_1LE1RB_0LB0LF_0RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1549: ~halts (TM_from_str "1RB0LF_1RC1RA_1LD0RF_1RF1LE_---1LD_0RB1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1550: ~halts (TM_from_str "1RB0RD_1LC---_1LE0RA_1RC0RF_1LD1LB_1RC0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1551: ~halts (TM_from_str "1RB1RA_1RC0RE_0LD0RA_0RE0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1552: ~halts (TM_from_str "1RB1LB_0RC0LA_1LD1RE_1RB0LB_1RC0RF_---0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1553: ~halts (TM_from_str "1RB0LC_1RC0RE_1LA0LD_1LC1LF_1RD0RC_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1554: ~halts (TM_from_str "1RB0LD_1RC1RE_1LA0LF_1LA0LC_1RA---_1LA0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1555: ~halts (TM_from_str "1RB1LA_1LC0RF_---0LD_1RE1LE_1RF1LC_1RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1556: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA1LE_---0LF_1RD1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1557: ~halts (TM_from_str "1RB0RC_0RC1RA_1LD1RB_0LE0LC_1RA0LF_1LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1558: ~halts (TM_from_str "1RB0RD_1RC0RC_1LD0LF_0RE0LD_0LC1RA_---0LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1559: ~halts (TM_from_str "1RB0RE_0RC0RA_1LD---_1LA0LB_1RA0LC_------") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1560: ~halts (TM_from_str "1RB1LD_0RC0RE_1LD0LA_0LA1LA_---0RF_1LD0RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1561: ~halts (TM_from_str "1RB0LC_1LA1RE_0LD0LF_0RB0RA_0LD1RB_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1562: ~halts (TM_from_str "1RB0LC_1LC0RE_1LF0LD_1LE---_1RB0RA_1LE0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1563: ~halts (TM_from_str "1RB1LA_0LC0RF_1RA0LD_1RC0LE_---1LC_1RC1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1564: ~halts (TM_from_str "1RB1RD_1LC0RD_1LD1LB_0RA1LE_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1565: ~halts (TM_from_str "1RB0LF_1RC0RD_1LD0LE_0LA0LC_1LC0RA_0RE---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1566: ~halts (TM_from_str "1RB0LE_0RC1RA_1RD1RE_1LA1LE_0LD1RF_---0RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1567: ~halts (TM_from_str "1RB1RC_0RC1RA_1LD0RA_1LE1LC_0LF0LD_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1568: ~halts (TM_from_str "1RB1RF_1LC0RE_0LD1LC_0RA---_0RA1LF_1RA0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1569: ~halts (TM_from_str "1RB0RE_1RC0RA_1LD---_1LF1LA_1RA0LD_0RF0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1570: ~halts (TM_from_str "1RB1LA_1RC0RC_1LD1RF_0LF1LE_---0LA_0LA1RC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1571: ~halts (TM_from_str "1RB1LA_0LA1RC_1RB1RD_1RF0LE_1RB1LD_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1572: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_1RF---_1RB0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1573: ~halts (TM_from_str "1RB0RE_1LC0RE_---0LD_1LA0LB_1RF0LA_1RD1RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1574: ~halts (TM_from_str "1RB0RB_1RC1LC_0LD0RA_0LE1LB_1LB0LF_0LA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1575: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_---1LF_1LB1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1576: ~halts (TM_from_str "1RB---_1RC0RD_1LD0LE_0LA0LC_1LF0RA_0LB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1577: ~halts (TM_from_str "1RB0RC_1LC0RF_1RA0LD_1LC0LE_0LF---_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1578: ~halts (TM_from_str "1RB---_0LC1RD_1LE1LD_1LC0RB_1RF0LB_0RA1RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1579: ~halts (TM_from_str "1RB0RF_1LC1RA_---0LD_1RA0LE_1LA1LD_1RB0RB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1580: ~halts (TM_from_str "1RB1LC_1RC1RD_0LA1RB_1LD0RE_---1RF_1LF0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1581: ~halts (TM_from_str "1RB1RC_1LC1RD_0RA0LD_1RA0LE_1RD0LF_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1582: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_1LE0RB_1RC0LF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1583: ~halts (TM_from_str "1RB0LD_1RC1LC_1LA1LF_1LF1LE_0LB---_0LA0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1584: ~halts (TM_from_str "1RB---_1RC0LE_1RD1RA_1LB0LF_1RB0LD_1LB0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1585: ~halts (TM_from_str "1RB0LF_1LC1RC_0RE1RD_---0RB_1LA1RE_1LE1LF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1586: ~halts (TM_from_str "1RB1RF_1LC---_1LE0RD_0RC0LC_0RA0LB_0RB1RD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1587: ~halts (TM_from_str "1RB0RF_0RC0RA_1LD---_0RE0LB_1LA1LE_1RA0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1588: ~halts (TM_from_str "1RB0RF_1LC0RE_1LA0LD_1LC---_1LB0RA_1RB0LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1589: ~halts (TM_from_str "1RB1RC_1LC1LD_1RA0LD_0LB1RE_1RF0RA_---1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1590: ~halts (TM_from_str "1RB0LE_0RC0RB_1LD0RD_0LA1LF_1LA---_0LC0RF") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1591: ~halts (TM_from_str "1RB0LC_0LA0RD_1LA1LB_1RC1RE_1RC1RF_1RA---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1592: ~halts (TM_from_str "1RB1LC_1RC---_1LA0RD_0LA0LE_1LD1RF_0RE1LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1593: ~halts (TM_from_str "1RB1RC_1LA1RA_---0RD_1LE1RB_0LF0LD_1LA0LD") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1594: ~halts (TM_from_str "1RB0RF_1LC1RE_1LA0LD_1RD1RB_0RD1RA_---0LC") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1595: ~halts (TM_from_str "1RB1RE_1RC0RF_0LD---_0LE1LD_1RA0LF_0RA1LE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1596: ~halts (TM_from_str "1RB0LD_1RC1RE_0RD1RB_1LE1RC_0LA1RF_---1LA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1597: ~halts (TM_from_str "1RB0RF_1RC1RE_1LD0LD_0RB1LC_1RB0RA_---1RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1598: ~halts (TM_from_str "1RB1RF_0RC0LA_1RD0RE_1LE1RC_---0LF_1LF0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1599: ~halts (TM_from_str "1RB0RC_1LC0LF_1LD0LB_1RE---_1RA1RE_1LC0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1600: ~halts (TM_from_str "1RB1RE_1LC1RB_1RA0LD_1LB1LD_1RF0RA_---0RE") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1601: ~halts (TM_from_str "1RB0RC_1LC1RD_---0LD_0LE1RF_1RF1LD_1RD0RA") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1602: ~halts (TM_from_str "1RB1LB_0LC0RD_0LE1LA_1RA0RA_1LA0LF_0LD---") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1603: ~halts (TM_from_str "1RB0LF_1LC0RE_---1LD_1LA0LA_1RB1RE_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1604: ~halts (TM_from_str "1RB1RA_1LC0RA_---1LD_1LE0LE_1RB0LF_1RE0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1605: ~halts (TM_from_str "1RB1RA_1LC0RA_---1LD_1LE0LE_1RB0LF_1RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

Lemma nonhalt1606: ~halts (TM_from_str "1RB0LF_1LC0RE_---1LD_1LA0LA_1RB1RE_1RA0LB") c0.
Proof. solve_hlin_nonhalt. Time Qed.

