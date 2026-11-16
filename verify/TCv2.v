Require Import List.
From BusyCoq Require Import Individual62.
Require Import NArith.
From BusyCoq Require Import TC62.

Definition TC_param (T:N) := [([T],O)].

Ltac solve_TC T :=
  apply (decide_TC_spec _ (TC_param T));
  native_cast_no_check (eq_refl true).

Lemma tm1: ~halts (TM_from_str "1RB---_1RC0RE_1LD1RF_0LE0LD_1RE0RC_1RA0RC") c0.
Proof. solve_TC 196238247%N. Time Qed.

Lemma tm2: ~halts (TM_from_str "1RB0RA_1LC0RB_1LF0LD_1LE---_1RA1LE_0LC0RF") c0.
Proof. solve_TC 202726523%N. Time Qed.

Lemma tm3: ~halts (TM_from_str "1RB1LF_0RC0RB_1LC0LD_1LE1LA_1LA---_1LD1LC") c0.
Proof. solve_TC 655286981%N. Time Qed.

Lemma tm4: ~halts (TM_from_str "1RB1LF_0RC0RB_1LC0LD_0LE1LA_1RF---_1LD1LC") c0.
Proof. solve_TC 806276267%N. Time Qed.

Lemma tm5: ~halts (TM_from_str "1RB1RC_1RC1RB_1LD0RA_---1LE_1LF0LA_1RD0LC") c0.
Proof. solve_TC 574934415%N. Time Qed.

Lemma tm6: ~halts (TM_from_str "1RB0RC_1RC0RE_1LD1RA_0LE0LD_1RF0RC_1RE---") c0.
Proof. solve_TC 359205467%N. Time Qed.

Lemma tm7: ~halts (TM_from_str "1RB1RF_1LC0RA_1RE1LD_0LB0LD_---0RC_1LA1RA") c0.
Proof. solve_TC 977242608%N. Time Qed.

Lemma tm8: ~halts (TM_from_str "1RB1LF_1LC0RE_---1LD_1LE0LA_1LA1RE_0LD0LB") c0.
Proof. solve_TC 448799935%N. Time Qed.

Lemma tm9: ~halts (TM_from_str "1RB0LC_0RC0RA_1LD0RB_1LE0LF_0LA1LD_0RB---") c0.
Proof. solve_TC 3738997802%N. Time Qed.

Lemma tm10: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_0RE1RD") c0.
Proof. solve_TC 1319931344%N. Time Qed.

Lemma tm11: ~halts (TM_from_str "1RB---_0RC0LA_1RD0RB_1LE0LE_1LF1LD_1RC1LB") c0.
Proof. solve_TC 2580145814%N. Time Qed.

Lemma tm12: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_1RE1RD") c0.
Proof. solve_TC 1319931992%N. Time Qed.

Lemma tm13: ~halts (TM_from_str "1RB1LC_0RC1LF_1LD0RE_0LA0LE_0LA0LB_1RA---") c0.
Proof. solve_TC 981368293%N. Time Qed.

Lemma tm14: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_0LE---") c0.
Proof. solve_TC 981155605%N. Time Qed.

Lemma tm15: ~halts (TM_from_str "1RB0RD_1LC0RC_1RA1LD_1RE0LF_---1RB_0LB0RF") c0.
Proof. solve_TC 3359425129%N. Time Qed.

Lemma tm16: ~halts (TM_from_str "1RB0LE_1LB0RC_0RF1RD_1LA1RD_1LA1LE_---0RB") c0.
Proof. solve_TC 2711621004%N. Time Qed.

Lemma tm17: ~halts (TM_from_str "1RB0LF_1LC1RE_1LA1LD_0LB1LB_1LB0RE_---0LD") c0.
Proof. solve_TC 937878358%N. Time Qed.

Lemma tm18: ~halts (TM_from_str "1RB0LC_1RC0RD_1LA0RC_1RE1RC_0LF1RB_---1LE") c0.
Proof. solve_TC 1629017566%N. Time Qed.

Lemma tm19: ~halts (TM_from_str "1RB1LE_1RC0RE_1LD0LD_1LA1LC_0RB0LF_1RE---") c0.
Proof. solve_TC 2580144533%N. Time Qed.

Lemma tm20: ~halts (TM_from_str "1RB0LE_0RC1RA_1RD0RF_1LA0LE_0LD0LC_0RA---") c0.
Proof. solve_TC 1403289720%N. Time Qed.

Lemma tm21: ~halts (TM_from_str "1RB0RD_1LC0RC_1RA1LD_0RE0LF_---0LC_0LB1LC") c0.
Proof. solve_TC 3539060623%N. Time Qed.

Lemma tm22: ~halts (TM_from_str "1RB1LC_0RC1LF_1LD0RE_0LA0LE_0LA0LB_0RE---") c0.
Proof. solve_TC 981155659%N. Time Qed.

Lemma tm23: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA0RF_0RC0RD_0RA---") c0.
Proof. solve_TC 981368237%N. Time Qed.

Lemma tm24: ~halts (TM_from_str "1RB1LC_0RC1LE_1LD0RF_0RB0LF_0LA---_0LA0LB") c0.
Proof. solve_TC 1159143663%N. Time Qed.

Lemma tm25: ~halts (TM_from_str "1RB1LC_0RC0LF_1LD0RE_0LA0LE_0LA0LB_0RC---") c0.
Proof. solve_TC 980943025%N. Time Qed.

Lemma tm26: ~halts (TM_from_str "1RB0RA_0LC0LD_1RA1LB_---1LE_1LE1LF_1LC1RF") c0.
Proof. solve_TC 1689841576%N. Time Qed.

Lemma tm27: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA---_0RC0RF_0LA0RD") c0.
Proof. solve_TC 980942973%N. Time Qed.

Lemma tm28: ~halts (TM_from_str "1RB1RD_0RC---_1LD0RA_0RE0LF_1RB1LC_0LD0RB") c0.
Proof. solve_TC 2971649656%N. Time Qed.

Lemma tm29: ~halts (TM_from_str "1RB0RB_1RC1RA_1LD1RE_1LA0LE_0LD0RF_1LE---") c0.
Proof. solve_TC 2580144959%N. Time Qed.

Lemma tm30: ~halts (TM_from_str "1RB1RF_0RC1RA_1LD0RE_0LE0LC_1RA0LD_1LC---") c0.
Proof. solve_TC 3686017381%N. Time Qed.

Lemma tm31: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_0RA1RD") c0.
Proof. solve_TC 1319931331%N. Time Qed.

Lemma tm32: ~halts (TM_from_str "1RB1RC_0LC0RE_0RD0LB_1RE1LF_0RF---_1LC0RA") c0.
Proof. solve_TC 1319931979%N. Time Qed.

Lemma tm33: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_0LE1RD") c0.
Proof. solve_TC 1319931969%N. Time Qed.

Lemma tm34: ~halts (TM_from_str "1RB0RF_0RC1RA_1LD0RE_0LE0LC_1RA0LD_0LD---") c0.
Proof. solve_TC 3508492237%N. Time Qed.

Lemma tm35: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_0RC---") c0.
Proof. solve_TC 980730341%N. Time Qed.

Lemma tm36: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_0LD1RD") c0.
Proof. solve_TC 2971649675%N. Time Qed.

Lemma tm37: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA1RF_0RC0RD_1LC---") c0.
Proof. solve_TC 981368237%N. Time Qed.

Lemma tm38: ~halts (TM_from_str "1RB1LC_0RC1LF_1LD0RE_0LA0LE_0LA0LB_0LA---") c0.
Proof. solve_TC 980730391%N. Time Qed.

Lemma tm39: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RE_0LA0LE_0LA0LF_0RC0LB") c0.
Proof. solve_TC 980943025%N. Time Qed.

Lemma tm40: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_0LA1RD") c0.
Proof. solve_TC 1319931957%N. Time Qed.

Lemma tm41: ~halts (TM_from_str "1RB---_1RC1RB_1LD0LE_1RF0LC_0LD0RD_0RB1RA") c0.
Proof. solve_TC 1034075929%N. Time Qed.

Lemma tm42: ~halts (TM_from_str "1RB0RD_1LC0RC_1RA1LD_1RE0LF_---1RB_0LB1LC") c0.
Proof. solve_TC 3007390535%N. Time Qed.

Lemma tm43: ~halts (TM_from_str "1RB1LA_1LC1RD_1LD0LC_0RB0RE_---1RF_1RF1RA") c0.
Proof. solve_TC 1689841581%N. Time Qed.

Lemma tm44: ~halts (TM_from_str "1RB1LC_0RC---_1LD0RF_0RA0LE_0LD0RB_1RB1RD") c0.
Proof. solve_TC 2971649657%N. Time Qed.

Lemma tm45: ~halts (TM_from_str "1RB---_1RC1LD_0RD1LA_1LE0RF_0LB0LF_0LB0LC") c0.
Proof. solve_TC 981368420%N. Time Qed.

Lemma tm46: ~halts (TM_from_str "1RB0RE_1LC0LC_1LD1LB_1RA1LE_0RA0LF_1RE---") c0.
Proof. solve_TC 2580145386%N. Time Qed.

Lemma tm47: ~halts (TM_from_str "1RB1RE_1LC1RD_1LE0LD_0LC0RF_1RA0RA_1LD---") c0.
Proof. solve_TC 2580144110%N. Time Qed.

Lemma tm48: ~halts (TM_from_str "1RB0LE_0RC0RE_1LD1RA_0LA0RF_0RC0RD_0LA---") c0.
Proof. solve_TC 980942973%N. Time Qed.

Lemma tm49: ~halts (TM_from_str "1RB0LF_0LC0RF_0LA1RD_0RE---_1LC1RA_0RE0RC") c0.
Proof. solve_TC 1159143601%N. Time Qed.

Lemma tm50: ~halts (TM_from_str "1RB0LA_1RC1LA_1RD1RF_1LB0RE_---0RF_0RB1RB") c0.
Proof. solve_TC 923150391%N. Time Qed.

Lemma tm51: ~halts (TM_from_str "1RB1LC_0RC0LF_1LD0RE_0LA0LE_0LA0LB_0LC---") c0.
Proof. solve_TC 981368293%N. Time Qed.

Lemma tm52: ~halts (TM_from_str "1RB0LE_1RC0RF_0RD0RE_1LE0RA_0LA0LD_0LE---") c0.
Proof. solve_TC 5019396041%N. Time Qed.

Lemma tm53: ~halts (TM_from_str "1RB0RF_0RC0RD_1LD0RE_0LE0LC_1RA0LD_0LD---") c0.
Proof. solve_TC 5925935327%N. Time Qed.

Lemma tm54: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0LF_1LC1LE_0LC0LA_---0RB") c0.
Proof. solve_TC 6749391479%N. Time Qed.

Lemma tm55: ~halts (TM_from_str "1RB0RD_1LC0LD_0RA1LD_1LB1LE_1RF0RC_---1RE") c0.
Proof. solve_TC 4923778803%N. Time Qed.

Lemma tm56: ~halts (TM_from_str "1RB0LE_1RC1RF_0RD0RE_1LE0RA_0LA0LD_1LD---") c0.
Proof. solve_TC 5265081255%N. Time Qed.

Lemma tm57: ~halts (TM_from_str "1RB0LC_0RC0RA_1LD0RB_1LE0LF_0LA0LB_0RB---") c0.
Proof. solve_TC 5903376709%N. Time Qed.

Lemma tm58: ~halts (TM_from_str "1RB---_1RC0LD_0RD0RB_1LE0RC_1LF1LA_0LB1LE") c0.
Proof. solve_TC 4714067737%N. Time Qed.

Lemma tm59: ~halts (TM_from_str "1RB0LE_1RC0RF_0RD1RB_1LE0RA_0LA0LD_0LE---") c0.
Proof. solve_TC 4487025307%N. Time Qed.

Lemma tm60: ~halts (TM_from_str "1RB1RF_0RC0RD_1LD0RE_0LE0LC_1RA0LD_1LC---") c0.
Proof. solve_TC 6216023989%N. Time Qed.

Lemma tm61: ~halts (TM_from_str "1RB0LC_0RC0RA_1LD0RB_1LE1LF_0LA0LB_1RA---") c0.
Proof. solve_TC 6192366131%N. Time Qed.

Lemma tm62: ~halts (TM_from_str "1RB0LC_0RC0RA_1LD0RB_1LE1LF_0LA1LD_1RA---") c0.
Proof. solve_TC 3928105566%N. Time Qed.

Lemma tm63: ~halts (TM_from_str "1RB0LC_1RC1RA_1LD0RB_---0LE_0LF1LA_0RA0LC") c0.
Proof. solve_TC 12431730476%N. Time Qed.

Lemma tm64: ~halts (TM_from_str "1RB0RE_1RC0RB_1LD0RA_0LE0LC_0RB1RF_0RD---") c0.
Proof. solve_TC 10567415294%N. Time Qed.

Lemma tm65: ~halts (TM_from_str "1RB0LE_0RC0RA_0LD1LF_1LA0LD_1LD0LC_0LB---") c0.
Proof. solve_TC 10567412334%N. Time Qed.



