From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.

Module Inductive62 := Inductive BB62.
Import Inductive62.

Lemma progress_rw tm c1 c2:
  progress tm c1 c2 <->
  Compute.TM.progress tm c1 c2.
Proof.
  split; intro H.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply Compute.TM.progress_step; eauto.
      destruct H; auto.
  - induction H.
    + constructor.
      destruct H; auto.
    + eapply progress_step; eauto.
      destruct H; auto.
Qed.

Ltac solve_rule :=
  unfold Config_WF; cbn;
  repeat rewrite List.Forall_cons_iff;
  repeat rewrite List.Forall_nil_iff;
  cbn;
  repeat split;
  intros;
  unfold s0;
  rewrite progress_rw;
  try (es; fail).

Ltac solve_hlin_nonhalt_T cfg T :=
  apply (decide_hlin_nonhalt_spec cfg T);
  [ solve_rule
  | native_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt cfg :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T (config_exploop cfg) 200000%N)
  end.


Lemma nonhalt63: ~halts (TM_from_str "1RB---_0RC0LE_1RD1RC_0RE0RB_0LF0LA_1LB1LD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 6 37).
Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB0RE_1RC0RE_0LD0RB_0LE1LA_1RA0RF_1LC---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB1RD_0LC1LE_1LD1LB_1RA1LF_---0RC_0LD0RE") c0.
Proof.
  solve_hlin_nonhalt default_config.
Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1LB---_0LC1LF_1RD0LB_0RE1LB_1LE0RD_0LA1LB") c0.
Proof.
  solve_hlin_nonhalt default_config.
Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB0LD_0RC1LD_1LC0RB_0LA1LE_0LF1LD_1LD---") c0.
Proof.
  solve_hlin_nonhalt default_config.
Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB1LC_1RC0RE_1LA0RD_---0LC_1RF1LE_1LD0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB0LE_1RC0LD_1RD0RA_1LB1RE_0RF---_0RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB0RB_1RC0LD_1RD0RA_1LB1RE_0RF---_0RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB0LC_1RC0RF_1LA1RD_0RE---_0RA1RC_1RA0LD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB0LC_1RC0RF_1LA1RD_0RE---_0RA1RC_1RA0RA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB0RD_1LC1RE_1RA0LB_1RC0LE_0RF---_0RC1RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB0RD_1LC1RE_1RA0LB_1RC0RC_0RF---_0RC1RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RA0RE_1RD0RF_1LB---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB0RE_0LC0RA_0LE1LD_1RA1LD_0RD0RF_1LB---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB1LA_1RC0RE_0LD0RB_0LE1LA_0RA0RF_1LC---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB---_1RC0LE_1LD0RB_0LC1LB_1RA0RF_0RE0RC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB0LD_1LC0RA_0LB1LA_1RE0RF_1RA---_0RD0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB0LD_1RC0RF_1LD1RB_1LA0RE_1LE1RD_1RC---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1LB0RE_1RC1LE_0LE0RD_1RB0RB_0RF1RA_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1LB0RE_1RC1LE_1LA0RD_1RB0RB_0RF1RA_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1LB0RE_1RC1LE_1LB0RD_1RB0RB_0RF1RA_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1LB0RE_1RC1LE_1LB0RD_1RB0RB_0RF1RA_---0LC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1LB0RC_1RA1LD_1RB0RB_0RF1RE_1LF0RD_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB---_1LC1RF_1LE0RD_1LD1RC_1RF0LC_1RB0RA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 37).
Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1LB1RF_1RC0LA_0LE0RD_1RB0LF_0RB1RA_0RE---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1LB0RC_1RA0LD_1RB0RB_1LB1RE_0RF---_0RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1LB0RC_1RA0LD_1RB0LE_1LB1RE_0RF---_0RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1LB1RF_1RC0LA_0LE0RD_1RB0RB_0RB1RA_0RE---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1LB0RF_0LC0LD_0LD1LE_0RE0LF_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0LE_1RC0RF_1RD1RB_1LD1RE_1LA0RD_1RC---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB---_1LC0RE_0LF0LD_0RA0LE_0RB0RC_0LD1LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0RB_1RC0LD_1LA0RA_1LB1RE_0RF---_0RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1LB0RF_1RC0LA_1RE0RD_1RE---_1RF1RC_1LF1RA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1LB0RF_0LC0LD_0LD1LE_0RE1LB_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB---_1LC0RE_0LF0LD_0RA1LC_0RB0RC_0LD1LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1LB0RF_0LC1RA_0LD1LE_0RE0LF_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB0RF_0LC1RA_0LD0LE_0RE0LF_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF1LA_0RA0LD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF0LA_0RA0LD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB---_0RC0RF_1RD1RA_0LE0RB_1LB0LE_1LD1LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB0RD_1LC0RF_1RA1LB_1RE1LD_1LF0RA_---0LB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1LC_1RC0RE_1LA0RD_---0LC_1RF1LE_0LD0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1LB0RF_1RC1LA_1RA0RD_1RE1LD_1LF0RC_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1LB0RF_0LC1RA_0LD0LE_0RE1LB_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1LB0RF_0LC1RA_0LD1LE_0RE1LB_1RA---_0RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB0RF_1RC0RB_0RD0RA_0LE1LB_0LA1LC_1LD---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF1LA_0RA1LC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB---_1LC0RD_0LE1RB_0RB0RC_0LF0LA_0RA1LC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB0LE_1RC1RE_---0RD_1LA1RF_1LA0RB_1RD1LC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1LB0RC_1LC0LA_1RD1RA_---0RE_1LB1RF_1RE1LD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB---_0RC1RF_1RD1RA_0LE0RB_1LB0LE_1LE1RF") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB---_0LC0RF_0LD1LE_0RE0RA_1RF1LE_1RB0RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1LB1RE_1RC0LA_1RA0RD_1RB0RB_0RF---_0RB1RA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1LB1RE_1RC0LA_1RA0RD_1RB0LE_0RF---_0RB1RA") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0RF_1RC0RA_1RD0RA_0LE0RC_0LA1LB_1LD---") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 2 0).
Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0RC_1LC0RD_0LD1RA_1RE0LF_0RB---_1LB1LC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1LB0RC_0LC1RF_1RD0LE_0RA---_1LA1LB_1RA0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0LE_0RC---_1LD0RA_0LA1RF_1LC1LD_1RC0RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1LB1LC_1LC0RD_0LD1RF_1RE0LA_0RB---_1RB0RC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1LB0RF_1RC0LE_0RD0RB_1RA---_1RF1LA_1RB1RD") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB---_1LC0RE_1RF0LD_1RE1LB_1RC1RA_0RA0RC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1LF_1RC1RE_1RD0LA_0RE0RC_1RF---_1LC0RB") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 37).
Time Qed.

Lemma nonhalt1: ~halts (TM_from_str "1RB0LE_0RC0RA_1RD---_1LA0RF_1RF1LD_1RA1RC") c0.
Proof.
  solve_hlin_nonhalt (config_arithseq_fixed_block_size 0 3 0).
Time Qed.


