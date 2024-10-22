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
  | vm_cast_no_check (eq_refl true)].

Ltac solve_hlin_nonhalt cfg :=
  match goal with
  | |- ~halts (TM_from_str ?x) c0 =>
    idtac x;
    (solve_hlin_nonhalt_T cfg 200000%N)
  end.




Lemma nonhalt1: ~halts (TM_from_str "1LB1LF_1LC0LA_0RD1RA_1LE1RD_1LD0RC_---1RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 7450%N 5 A A A A [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1LB1LF_1LC0LA_0RD1RA_1LE1RD_1LE0RC_---1RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 7450%N 5 A A A A [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1LB---_0LC1RE_0RD1LF_1LC1RB_0RF0RA_0LA0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 5604%N 3 A B A B [0] [1] [0;1;0] [1] [0;0;1;1] [0;0;1;0] [0]). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1LB_0LC0RE_1LE0RD_1RE---_0LA1RF_0RB0RC") c0.
Proof. solve_hlin_nonhalt (config_SBC 5659%N 3 C E C E [0] [1] [0;1;0] [1] [0;0;1;1] [0;0;1;0] [0]). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB---_0LC1RF_0RA1LD_0LE0RB_1LB---_0RD0RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 5502%N 3 E B E B [0] [1] [0;1;0] [1] [0;0;1;1] [0;0;1;0] [0]). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB1RF_0LC1RF_0RA1LD_0LE0RA_1LB---_0RD0RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 5358%N 3 E A E A [] [] [0;1] [] [0;0;1;1] [0;0;1;0] [0]). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB1RF_0LC1RF_1LF1LD_0LE0RA_1LB---_0RD0RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 1585%N 3 B D B D [] [] [1;0] [] [0;1;1;0] [0;1;0;0] [0]). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1LB---_1LC0LA_0RD1RE_1LE1RD_1LF0RC_0LD0LA") c0.
Proof. solve_hlin_nonhalt (config_SBC 6188%N 5 A E A E [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1LB---_1LC0LA_0RD1RE_1LE1RD_1LF0RC_1LE0LA") c0.
Proof. solve_hlin_nonhalt (config_SBC 6158%N 5 A E A E [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1LB---_1LC0LA_0RD1RF_1LE1RD_1LD0RC_1LB0RC") c0.
Proof. solve_hlin_nonhalt (config_SBC 6158%N 5 A F A F [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1LB0RC_1LC0LF_0RD1RA_1LE1RD_1LE0RC_1LB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 6158%N 5 F A F A [0] [1] [0;1;0] [1] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC1LE_0RF---_0RD0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 3476%N 5 E B E B [1;1] [0;1] [1;1;1;0;1] [0;1] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC1RE_---1LF_0RD0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 3480%N 5 C B C B [0;1] [0;1] [0;1;1;0;1] [0;1] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB---_1LC0RD_1RD0LC_0RE0LF_0LB1RF_0RB1RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1831%N 5 C B C B [0;1;0] [0;1;0] [0;1;0;1;0] [0;1;0] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_1LD0RA_0RD---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1839%N 5 B A B A [0;1;0] [0;1;0] [0;1;0;1;0] [0;1;0] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1LB1RA_1RC0LE_1RE0RD_0RC1RF_0LA0RA_0LB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2126%N 4 E C E C [0;1;0] [0;0;1] [0;1;0;1;0;0] [0;0;1] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB0LA_0LC0RC_0RE0RD_1RE---_1LF0RA_0LA0LE") c0.
Proof. solve_hlin_nonhalt (config_SBC 1268%N 5 E A E A [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB1RC_1LC0RE_1LD0RA_0LA0LC_0RC0RF_0LA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 5188%N 5 C A C A [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1LB1RE_1RC1LD_1RA0RC_0LA0LE_0RD0RF_1RC---") c0.
Proof. solve_hlin_nonhalt (config_SBC 769%N 5 E C E F [0] [1] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1LB1RE_1RC1LD_1RA0RC_0LA0LF_0RD0RB_0RD---") c0.
Proof. solve_hlin_nonhalt (config_SBC 769%N 5 F C F B [0] [1] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB0LD_0RC0RF_1RD0RA_1LE0RC_1LA1LE_---1RC") c0.
Proof. solve_hlin_nonhalt (config_SBC 3076%N 4 E F E F [] [] [1;0;1] [] [0;1;0;0;1;1] [0;1;0;0;1;0] [0;1]). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB0RA_1LC1RE_1RA1LD_0LB0RF_0RD0RC_---1LD") c0.
Proof. solve_hlin_nonhalt (config_SBC 788%N 5 B C B C [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LE_0RD0RF_1RB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 789%N 5 E B E F [0] [1] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC0LE_0RD---_0RD0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 789%N 5 E B E A [0] [1] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_1LA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 483%N 5 A D A C [0;1;0] [0;1;0] [0;1;0] [0] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD0RF_0LE---") c0.
Proof. solve_hlin_nonhalt (config_SBC 485%N 5 A D A C [0;1;0] [0;1;0] [0;1;0] [0] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB1RA_0RC0RF_0LD---_1LE1RE_0RD1LF_1RA0LD") c0.
Proof. solve_hlin_nonhalt (config_SBC 2249%N 5 F F F B [1;1] [0;1] [1;1;0] [1] [1;1;0;1] [1;1;1;1] [1;1;1]). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD0RA_1LC---_1LF1RF_0RE1LA") c0.
Proof. solve_hlin_nonhalt (config_SBC 2304%N 5 A A A C [1;1] [0;1] [1;1;0] [1] [1;1;0;1] [1;1;1;1] [1;1;1]). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1LB1RE_0LC0LB_1RD1LB_0RA---_0RF0LB_1RA0RD") c0.
Proof. solve_hlin_nonhalt (config_SBC 465%N 3 B A B A [] [] [1;0] [] [0;0;0;1] [0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB1RC_1LC0RE_1LD0RA_0LA0LC_0RC1RF_1LC---") c0.
Proof. solve_hlin_nonhalt (config_SBC 4660%N 5 C A C A [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB1RE_0LC0RC_0RE1RD_1LE---_1LF0RA_0LA0LE") c0.
Proof. solve_hlin_nonhalt (config_SBC 4800%N 5 E A E A [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB1LC_1LA1RD_0LB1LA_0RE1RF_---0RA_0RA0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 2343%N 6 A F A D [1] [1] [1;1] [] [1;0;1;1;0;1] [1;1;1;1;1;1] [1;1;1;1;1]). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1LB1RA_1RC0LE_1RE0RD_0RC0RF_0LA0RA_0LE---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1950%N 4 E C E E [0;1;0] [0;0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1LB1RF_1RC0LE_1RE0RD_0RC0LE_0LA0RA_1LB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1950%N 4 E D E E [0;1] [0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1LB1RF_1RC0LE_1RE0RD_0RC0LE_0LA0RA_1LD---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1950%N 4 E D E E [0;1] [0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1LB1RE_0LC0LB_1RD1LB_0RA---_0RF1RF_1RA0RD") c0.
Proof. solve_hlin_nonhalt (config_SBC 2085%N 3 B A B A [] [] [1;0] [] [0;0;0;1] [0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1LB0RC_1RC0LB_0RD1RA_0LA1RE_0RA1RF_1RB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1447%N 5 B D B C [0] [0] [0;1] [] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0LD_0RF0LD_1RC0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 615%N 3 D C D C [] [] [1;0] [] [0;0;0;1] [0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB1LD_0RC---_1LD1RE_0LA0LD_0RF1RF_1RC0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 769%N 3 D C D C [] [] [1;0] [] [0;0;0;1] [0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1LB0RD_1LC1RE_1RA0LB_1RE1RB_0RC0RF_0RA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2482%N 8 C A C E [1;0] [0;0] [1;0] [] [1;0;0;0] [1;0;1;0] [1;0;1]). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB0RE_1RC1RF_1LD0LC_1RE1LC_1LB0RB_---0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 762%N 3 D F D F [] [] [1;1] [] [1;0;0;0] [1;0;1;0] [1;0;1]). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB0LA_0RC1RD_0LD1RE_1LA0RB_0RD1RF_1RA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 5007%N 5 A C A B [0] [0] [0;1] [] [0;0;1;0] [1;0;1;0] [1]). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB0LB_0RC1LD_1LD1RA_0LA0RE_0RC1RF_0RD---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1237%N 3 B A B C [0] [1] [0;0;1;0] [] [0;0;0;1;0;1] [0;1;0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1LB1RC_0LC0RE_1RD0LD_0RA1LB_0RA1RF_0RB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 3725%N 3 D C D A [0] [1] [0;0;1;0] [] [0;0;0;1;0;1] [0;1;0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1LB0LC_1RC1LE_0RD0RB_1RA1RF_0LF---_0LA0RC") c0.
Proof. solve_hlin_nonhalt (config_SBC 4518%N 3 A B A B [] [] [0;0;1;1] [] [0;1;0;0;0;1;0;1] [0;1;0;0;0;1;0;0] [0;1]). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB1RE_1LC0LF_1RF1LD_0LE---_0LB0RF_0RA0RC") c0.
Proof. solve_hlin_nonhalt (config_SBC 4643%N 3 B C B C [] [] [0;0;1;1] [] [0;1;0;0;0;1;0;1] [0;1;0;0;0;1;0;0] [0;1]). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB---_1LC0RD_0LD0LB_1RE1RB_1LB0RF_0RB0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 4129%N 5 B D B D [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB---_1LC0RD_0LD0LB_1RE1RB_0LF0RF_0RB0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 4129%N 5 B D B D [] [] [0;1] [] [0;0;0;1] [0;1;0;1] [0;1;0]). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB1LC_1LA1RD_0LB1LA_0RE1RF_---0LB_0RA0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 1948%N 6 A D A D [] [] [1;1] [] [1;0;1;1;0;1] [1;1;1;1;1;1] [1;1;1;1;1]). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB1LC_1LA1RD_0LB1LA_1RE1RF_---0LC_0RA0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 1948%N 6 A D A D [] [] [1;1] [] [1;0;1;1;0;1] [1;1;1;1;1;1] [1;1;1;1;1]). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1LB---_1RC0LE_1RE0RD_0RC0LA_0LF0RF_1LB1RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1670%N 4 E D E E [0;1] [0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1LB---_1RC0LE_1RE0RD_0RC0LF_0LF0RF_1LB1RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1670%N 4 E D E E [0;1] [0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB0RD_0RC0RB_0LD1RA_1LE---_0LF0RB_0LA1LC") c0.
Proof. solve_hlin_nonhalt (config_SBC 2074%N 5 C C C C [] [] [1;0] [] [0;0;1;1] [0;0;0;1] [0;0;0]). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1LB1RE_1RC1LD_1RA0RC_0LA0LA_0RD0RF_1RC---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1918%N 5 A F A F [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1LB1RE_1RC1LD_1RA0RC_0LA0LF_0RD0RB_1LB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1918%N 5 F B F B [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RE_0LC0LC_0RD0RF_1RB---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2074%N 5 C F C F [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB1LD_1RC0RB_1LA1RF_0LC0LE_1LA---_0RD0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 2074%N 5 E A E A [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB0LD_1RC1LA_1RD0RC_1LB1RE_0RA0RF_1RC---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2074%N 5 D F D F [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB0RA_1LC1RE_1RA1LD_1RC0LB_0RD0RF_1RA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2347%N 5 B F B F [] [] [0;1;1] [] [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1]). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB1RF_0RC0RA_1RD0LE_1LC1RA_1LC1LE_---0RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 2789%N 2 E A E C [] [] [0] [] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB0LC_1LA1RD_1LA1LC_1RE1RF_0RA0RD_---0RE") c0.
Proof. solve_hlin_nonhalt (config_SBC 2767%N 2 C D C A [] [] [0] [] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB0RF_0RC0RA_1RD0LE_1LC1RA_1LC1RD_---1RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3015%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB0RF_0RC0RA_1RD0LE_1LC1RA_1LC1RE_---1RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3015%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB0RF_0RC0RA_1RD0LE_0LE1RA_1LC1RE_---1RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3057%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB1RF_0RC0RA_1RD0LE_1LC1RA_1LC1RD_---0LB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3109%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB1RF_0RC0RA_1RD0LE_1LC1RA_1LC1RE_---0LB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3109%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB1RF_0RC0RA_1RD0LE_0LE1RA_1LC1RE_---0LB") c0.
Proof. solve_hlin_nonhalt (config_SBC 3151%N 2 E B E B [0] [1] [0;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1LB1RF_1RC1RA_1RE0RD_0RC0LE_0LA0RA_1LD---") c0.
Proof. solve_hlin_nonhalt (config_SBC 2710%N 4 E D E E [0;1] [0;1] [0;1;0] [] [1;0;0;0;0;1] [1;0;0;1;0;1] [1;0;0;1]). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB0RC_1RC0LC_0RD0LE_1LE1RF_0LB---_0RA0LA") c0.
Proof. solve_hlin_nonhalt (config_SBC 2093%N 5 C F C D [0] [1] [0;0] [] [0;0;0;1] [0;1;0;1] [0;1]). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB0RE_1LB0LC_0LD1LC_1RD1RA_1RA0RF_---1RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1189%N 2 C A C A [1] [1] [1;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB0RE_1LB0LC_0LD1LC_1RD1RA_1RA1RF_---0LA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1241%N 2 C A C A [1] [1] [1;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB0RE_1RC0RA_1LC0LD_0LE1LD_1RF1RB_1RE---") c0.
Proof. solve_hlin_nonhalt (config_SBC 1173%N 2 D E D E [] [] [1] [] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB0RF_1RC0RA_1LC0LD_0LE1LD_1RE1RB_---1RB") c0.
Proof. solve_hlin_nonhalt (config_SBC 1173%N 2 D B D B [1] [1] [1;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1RB1RF_1RC0RA_1LC0LD_0LE1LD_1RE1RB_---0LB") c0.
Proof. solve_hlin_nonhalt (config_SBC 1225%N 2 D B D B [1] [1] [1;1] [1] [0;0;1] [1;1;1] [1;1]). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1LB1RE_1LC1LD_1RB0LF_0RC0RA_1RE0RD_1LA---") c0.
Proof. solve_hlin_nonhalt (config_SBC 3754%N 2 F D F D [0;1] [0;1] [0;1;1;1;0] [0;1] [0;1;1;0;0;1] [0;1;0;0;0;1] [0;1;0]). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1LB0RE_0RC1LA_1RE0LD_1LE---_0LB1RF_0RA0RD") c0.
Proof. solve_hlin_nonhalt (config_SBC 6493%N 3 B E B E [1] [1] [1;1;0] [1] [0;0;1;1] [0;0;1;0] [0]). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1RB1RC_1LC1RC_0RF0RD_1LB0LE_1LF---_0LD0RA") c0.
Proof. solve_hlin_nonhalt (config_SBC 1770%N 3 C F C F [1] [0] [1;1;0] [0] [1;1;0;0] [1;0;0;0] [1;0;0]). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1LB---_0LC1RE_0RD1LF_1RB0RB_0RF0RA_0LA1LC") c0.
Proof. solve_hlin_nonhalt (config_SBC 451%N 3 B B B B [1] [0] [1;0;1] [0] [0;1;1;0] [0;1;0;0] []). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1LB0RD_0LC0LD_1RD---_1RE1LF_1RA0RE_0RF0LA") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 3572%N 3 [
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;1] [] [] F E;
    side_binary_dec_ov0_rule [1;0;1;0] [1;0;1;1] [1;1] [1;0] [] [] F E;
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;0] [] [] F E;
    side_binary_dec_ov1_rule [1;0;1;0] [1;0;1;1] [1;0] [1;1] [1;0] [] F E
  ]).
Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1RB1LE_1RC0RB_1LD0RA_0LF0LA_0RE0LC_1RA---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 3611%N 3 [
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;1] [] [] E B;
    side_binary_dec_ov0_rule [1;0;1;0] [1;0;1;1] [1;1] [1;0] [] [] E B;
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;0] [] [] E B;
    side_binary_dec_ov1_rule [1;0;1;0] [1;0;1;1] [1;0] [1;1] [1;0] [] E B
  ]).
Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1RB0RA_1LC0RD_0LF0LD_1RA1LE_0RE0LB_1RD---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 3718%N 3 [
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;1] [] [] E A;
    side_binary_dec_ov0_rule [1;0;1;0] [1;0;1;1] [1;1] [1;0] [] [] E A;
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;0] [] [] E A;
    side_binary_dec_ov1_rule [1;0;1;0] [1;0;1;1] [1;0] [1;1] [1;0] [] E A
  ]).
Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1RB0LD_1RC1RB_1LA1RE_1LC1LA_0RB1RF_0LA---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 500%N 3 [
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1] [] [] A B;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1] [1;1] [1;0] [] A B;
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1;1] [] [] A B;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1;1] [1] [1;0] [] A B
  ]).
Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1RB1RA_1LC1RE_1RA0LD_1LB1LC_0RA1RF_0LC---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 300%N 3 [
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1] [] [] C A;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1] [1;1] [1;0] [] C A;
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1;1] [] [] C A;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1;1] [1] [1;0] [] C A
  ]).
Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1RB---_1RC1LF_1RD0RC_1LE0RB_0LA0LB_0RF0LD") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 400%N 3 [
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;1] [] [] F C;
    side_binary_dec_ov0_rule [1;0;1;0] [1;0;1;1] [1;1] [1;0] [] [] F C;
    side_binary_dec_inc_rule [1;0;1;0] [1;0;1;1] [1;0] [] [] F C;
    side_binary_dec_ov1_rule [1;0;1;0] [1;0;1;1] [1;0] [1;1] [1;0] [] F C
  ]).
Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1LB1RE_1RC0LD_1RA1RC_1LA1LB_0RC1RF_0LB---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 500%N 3 [
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1] [] [] B C;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1] [1;1] [1;0] [] B C;
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1;1] [] [] B C;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1;1] [1] [1;0] [] B C
  ]).
Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1LB1LC_1LC1RE_1RD0LA_1RB1RD_0RD1RF_0LC---") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 300%N 3 [
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1] [] [] C D;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1] [1;1] [1;0] [] C D;
    side_binary_dec_inc_rule [0;1;1;1] [1;1;1;1] [1;1] [] [] C D;
    side_binary_dec_ov1_rule [0;1;1;1] [1;1;1;1] [1;1] [1] [1;0] [] C D
  ]).
Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1LB0RD_1RC0LF_1RA1RD_0RE---_0LA1RB_0LD1LE") c0.
Proof. solve_hlin_nonhalt (config_SBC 487%N 5 F B F E [] [] [0] [0;1;1] [1;0;1;1] [1;0;0;1] []). Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1RB0LD_1RC1RF_1LA0RF_0LC1LE_0LC1RA_0RE---") c0.
Proof. solve_hlin_nonhalt (config_SBC 480%N 5 D A D E [] [] [0] [0;1;1] [1;0;1;1] [1;0;0;1] []). Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB1RF_1LC0LB_0RC1LD_1RE0LB_1RA0RE_---0RD") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 2010%N 4 [
    side_binary_dec_inc_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1] [] [] B D;
    side_binary_dec_ov1_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1] [] [] [] B D;
    side_binary_dec_inc_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [] [] [] B D;
    side_binary_dec_ov0_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [] [0;1;1;0;1] [0;1;1] [] B D
  ]).
Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RD") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 617%N 4 [
    side_binary_dec_inc_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1] [] [] B D;
    side_binary_dec_ov1_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [0;1;1;0;1] [] [] [] B D;
    side_binary_dec_inc_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [] [] [] B D;
    side_binary_dec_ov0_rule [0;1;1;0;0;1] [0;1;1;0;1;1] [] [0;1;1;0;1] [0;1;1] [] B D
  ]).
Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1LB0RE_1RC0LD_1RA0RB_0RF0LE_1RB1LD_---0LA") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 376%N 4 [
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [] [] E B;
    side_binary_dec_ov0_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [1] [] [] E B;
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [] E B;
    side_binary_dec_ov1_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [0;1;0] [] E B
  ]).
Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1LB0RF_0LC---_0RD0LF_1RE0LA_0RA0RB_1RD1LC") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 2400%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] F D;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0;0] [1] F E;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] F D;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] F D
  ]).
Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1LB0RF_0LC---_0RD0LF_1RE0LA_0RA0RD_1RD1LC") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 2300%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] F D;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0;0] [1] F E;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] F D;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] F D
  ]).
Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1RB1LE_1RC0LE_1RD0RB_1LB0RA_0RF0LA_---0LD") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 2120%N 4 [
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [] [] A B;
    side_binary_dec_ov0_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [1] [] [] A B;
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [] A B;
    side_binary_dec_ov1_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [0;1;0] [] A B
  ]).
Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1RB1LF_1RC0LD_0RD0RB_1LE0RA_0LF---_0RB0LA") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 4600%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] A B;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0] [] A B;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] A B;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] A B
  ]).
Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1RB1LF_1RC0LD_0RD0RE_1LE0RA_0LF---_0RB0LA") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 4700%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] A B;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0] [] A B;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] A B;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] A B
  ]).
Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1RB0LD_1RC0RA_1LA0RE_0RF0LE_1RA1LD_---0LC") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 2120%N 4 [
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [] [] E A;
    side_binary_dec_ov0_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [] [1] [] [] E A;
    side_binary_dec_inc_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [] E A;
    side_binary_dec_ov1_rule [1;0;1;1;0;1] [1;0;1;1;1;1] [1] [] [0;1;0] [] E A
  ]).
Time Qed.

Lemma nonhalt98: ~halts (TM_from_str "1RB0LC_0RC0RA_1LD0RF_0LE---_0RA0LF_1RA1LE") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 4700%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] F A;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0] [] F A;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] F A;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] F A
  ]).
Time Qed.

Lemma nonhalt99: ~halts (TM_from_str "1RB0LC_0RC0RD_1LD0RF_0LE---_0RA0LF_1RA1LE") c0.
Proof.
  solve_hlin_nonhalt (config_SBC' 4700%N 4 [
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [] F A;
    side_binary_dec_ov1_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [1] [] [0;1;0] [] F A;
    side_binary_dec_inc_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [] [] F A;
    side_binary_dec_ov0_rule [1;0;0;1;0;1] [1;0;0;1;1;1] [] [1] [] [] F A
  ]).
Time Qed.












