From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Inductive.
From BusyCoq Require Import UnaryCounter.

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

Ltac solve_hlin_nonhalt_T cfg T :=
  apply (decide_hlin_nonhalt_spec cfg T);
  [ unfold Config_WF; cbn;
    repeat rewrite List.Forall_cons_iff;
    repeat rewrite List.Forall_nil_iff;
    cbn;
    repeat split;
    intros;
    unfold s0;
    rewrite progress_rw;
    try (es; fail)
  | vm_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt cfg :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T cfg 200000%N)
  end.

Module Eat2Digit.

Lemma nonhalt1: ~halts (TM_from_str "1LB0LE_0LC1LD_1RA1LC_1RC---_1RF1LE_0RA0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [1;0] [0;0] [1]). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1LB0LE_0LC1LD_1RA1LC_1LC---_1RF1LE_0RA0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [1;0] [0;0] [1]). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1LB1LE_0LC1LD_1RA1LC_1RC---_1RF0LE_0RF0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [0;1] [0;0] [1]). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1LB1LE_0LC1LD_1RA1LC_1LC---_1RF0LE_0RF0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [0;1] [0;0] [1]). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB1LA_0RC0RB_1LD0LA_0LE1LF_1RC1LE_---1LE") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 A C [1;0] [0;0] [1]). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB1LA_0RC0RB_1LD0LA_0LE1LF_1RC1LE_---1RE") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 A C [1;0] [0;0] [1]). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1LB1RA_1LC0LD_1RD---_0LE1LD_1RF1LE_0RA0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [0] [0] [1]). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1LB1RA_1LC0LD_1RD---_1LE1LD_1RF0LE_0RF0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [1] [0] [1]). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1LB1RA_1LC0LD_1LD---_0LE1LD_1RF1LE_0RA0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [0] [0] [1]). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1LB1RA_1LC0LD_1LD---_0LE1LD_1RF1LE_0RA0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [0] [0] [1]). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1LB1RA_1LC0LD_1LD---_1LE1LD_1RF0LE_0RF0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 1 E A [1] [0] [1]). Time Qed.

End Eat2Digit.

Module Eat1Digit.

Lemma nonhalt1: ~halts (TM_from_str "1RB1LF_1RC0RB_1RD1RB_0LE0LF_---0LF_1LA1LD") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 F B [] [] [0;1]). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1LB0LA_1RC0LA_0LE0RD_0RC1LF_1RB0LD_1LE---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 A D [] [] [0;1]). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0RB_1LC0RB_0LD1LC_1RA0LE_1LF0RE_0LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [] [] [1;1]). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1LB1LC_1RC0LE_1LE0RD_1RB0RC_0RF0LA_1LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 E C [0] [0] [0;1]). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1LB1LC_1RC0LE_1LE0RD_1RB0RD_0RF0LA_1LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 E D [0] [0] [0;1]). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1LB---_1LC1LF_1RD0LB_1LB0RE_0RD1RC_1LC1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 B E [] [] [0;1]). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB1LD_1RC0LE_1LA0RF_---1LC_1LB1LE_0RC1RB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 E F [] [] [0;1]). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1LB0RE_1RC1LF_1LD1LC_1RA0LC_0RA1RD_---1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C E [] [] [0;1]). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1LB0RE_1LC1LF_1LD1LC_1RA0LC_0RA1RD_---1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C E [] [] [0;1]). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1LB0LE_1RC1LB_1RD0RC_1LA0LF_1LD---_0LE0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 B C [] [] [1]). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB0RA_1LC0RE_1LD0LC_1RA1LE_1LC1RF_---0RC") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 5 E A [] [] [0;0;1]). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB---_1LB0LA_---1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 E B [] [] [0;1;1] [0;0;1] []). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB---_0RF0LA_---1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 E B [1] [0] [0;1;1] [0;0;1] []). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1LB0LF_0LC0RB_1RD1LE_1RB1LA_0RD0LA_---1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 E B [1] [0] [0;1;1] [0;0;1] []). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB1LE_1RC0RB_0LC1LD_0LE1RD_0LA1LF_---1LA") c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1]).
  all: follow H; es.
Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB1LD_1RC0RB_0LD1RC_0LA1LE_0LF1LA_0LA---") c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1]).
  all: follow H; es.
Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1LD_1RC0RB_0LD1RC_0LA1LE_0LF1LA_0RC---") c0.
Proof.
  epose proof (LBouncerIncs' _ _ _ [] [1;1;1] [1;1;1; 1;1;1;1;1;0]) as H.
  solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 A C [1;1;1; 1;1;1;1;1;0] [1;0;0;0;0;0; 0;0;0] [0;0;0] [1;0;0] [1]).
  all: follow H; es.
Time Qed.

End Eat1Digit.

Module Others.

Lemma nonhalt1: ~halts (TM_from_str "1LB0RD_1RC1LF_0RD0RC_1LD1RE_0LB0LB_1LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 F C [] [] [0;0;1]). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB0LD_0RC0LC_1RD0LB_0RE0LE_1LF0RE_1LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 A E [1;1] [0;0] [1;0]). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB1LA_0LC0RF_---1LD_1LE1LF_1RA0LC_0LE0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 A F [1;1;1] [0;0;0] [1]). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1LA_0RC0RB_1RD---_0LE0LF_1LA1LF_0LD0RA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 A B [] [] [1]). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1LB0LF_0LC1LF_1RD0LC_0RD0RE_1RA---_0LA0RC") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C D [] [] [1]). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1LB0LF_1RC1LF_1RD1LC_---0RE_1RA0RE_0LA0RC") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C E [1] [0] [1]). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1LB1LF_1RC1LB_---0RD_1RE0RD_1LA0LF_0LE0RB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 B D [1] [0] [1]). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1LB0RB_0LC0LE_1LD0LB_1RE1LF_0RA0RE_1LC---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 5 F E [] [] [0;0;1]). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_0RF0LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_1RC0LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LC_1RA1LA_1RC0LF_---0LB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB0LD_1LC1LB_1RD0LF_---1RE_1LC0RE_0LB1LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 B E [] [] [1;1]). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1LB0LE_1RC1LA_0RD0RC_0RE1RB_1RF0LA_1RA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 6 A C [] [] [0;1]). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB1LA_0LC0RB_1RA1LD_0RB0LE_1LC0LF_---1LE") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 A B [1;1] [0;0] [1]). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB1LA_0LC1RD_---1LD_1LE1LF_1RA0LC_0LE0RF") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 A F [1;1;1] [0;0;0] [1]). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1LB1LF_1RC0LD_1LD0RC_0RE0LA_1LA1RB_1LD---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 D C [0] [0] [0;1]). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF1RC_1LC1LA_---0RD") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 B F [0] [0] [0;1]). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1LB0RA_0RC0LE_1LE1RD_1RA0LB_1LD1LF_0LD---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 B A [0] [0] [0;1]). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB0LB_1LC0RB_0LD1LC_1RA1LE_---1LF_1LC0LA") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB0LB_1LC0RB_0LF0RD_---1LE_1LC0LA_1RA1LD") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB1LD_1LC0RB_0LE0RA_1LC0LF_1RA1LA_---0LB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1LE_1LC0RB_0LD1LC_1RA1LA_1LC0LF_---0LB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 C B [1] [0] [1;1]). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB1LE_0RC0RB_1LC1RD_0LA0LC_1LF---_1LA0RC") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 E B [] [] [0;0;1]). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1LB0RD_1RC1LF_0RD0RC_1LD1RE_1LD0LB_1LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 4 F C [] [] [0;0;1]). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1LB1RE_0LC0RB_0LD1LA_0RE1LC_1RF0RA_1RB---") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 4 B B [1;1;0] [1;1;0] [1;1;0] [0;1;0] []). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1LB1LD_1RC1LF_1RD0RC_0LA0LE_0LA0RB_0LC---") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 2 B D [1;0] [1;0] [1;0;1;0;0] [1;0;0;0;0] [1]). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB1LF_0RC0LE_1LA1LD_1RE1RB_1LA0RD_0LB---") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 10000%N 5 B B [1;1] [1;0] [1;1;0] [1;0;0] [1]). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB1LC_1LA1RD_0LB1LE_1LC0RD_0LF1RB_0LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 10000%N 5 A D [0;0] [0;0] [0;0;1;1;0;0] [1;1;1;1;0;0] [1;1;1;1]). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1LB0LF_1LC0RD_1RB0LA_0LC0RE_1RF---_1RC1RD") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 5 A E [] [] [0;1;1] [0;0;1] [0;0;1]). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB1LF_1RC0RB_0LD0LE_1LA1LC_0LD0RA_0LB---") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 10000%N 2 F B [1] [1] [0;1;0;0;1] [0;0;0;0;1] []). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB---_0LC0RB_1RA1LD_1LE1LF_1LB0LC_0LE0LA") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 3 D B [1] [0] [0;0;1;1] [0;0;0;1] []). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1LB1LF_1LC0LD_0LD0RC_1RE1LA_1RC---_0LB0LE") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 1000%N 3 A C [1] [0] [0;0;1;1] [0;0;0;1] []). Time Qed.

End Others.



Module PeriodicBadDigit.

Lemma nonhalt1: ~halts (TM_from_str "1LB1LE_1LC0LA_1RD1LA_0LE0RD_0RC1LF_0LB---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 A D [] [] [0;0;1]). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1LF_1RC0RB_0LD0LE_1LA1LC_0LD0RA_1LD---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 F B [] [] [0;0;1]). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB1LF_0LC0RB_0RA1LD_0LE---_1LA0LF_1LE1LC") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 F B [] [] [0;0;1]). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1LB1LD_1LC0LA_1RD1LA_0LE0RD_0RC1LF_0LB---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 2 A D [] [] [0;0;1]). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1LB0RD_1LC0LE_1RA0LF_0RA1RC_---0LB_1LC0LD") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 F D [] [] [0;1]). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1LB0LE_1RC0LF_1LA0RD_0RC1RB_---0LA_1LB0LD") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 F D [] [] [0;1]). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0LC_0LC0RE_1LA1LD_1LA1LF_0RB1RA_0LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C E [] [] [0;1]). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1LB1LE_1RC0LA_1LA0RD_0RC1RB_1LB1LF_0LB---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 A D [] [] [0;1]). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0LC_1LC0RE_1LA1LD_1LA1LF_0RB1RA_0LA---") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000%N 3 C E [] [] [0;1]). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1LF1LE_0LF0LB_1LC0LA") c0.
Proof. solve_hlin_nonhalt (config_BEC_Pos 10000%N 3 D C [] [] [0;0;1;1] [0;0;0;1] []). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB1LF_0LC0RB_0RA1LD_0LE---_1LA0LF_1LE1LB") c0.
Proof. solve_hlin_nonhalt (config_BEC 1000000%N 2 F B [] [] [0;0;1]). Time Qed.

End PeriodicBadDigit.






