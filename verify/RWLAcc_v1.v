From BusyCoq Require Import RWLAcc62.

Ltac solve_nonhalt bsz bmaxT mnc T :=
  eapply (decide_nonhalt_spec _ bsz bmaxT true mnc T);
  native_cast_no_check (eq_refl true). 


Lemma nonhalt1: ~halts (TM_from_str "1RB0LA_1RC0RD_1RD0RC_1LE1RF_---1LA_1RA0LC") c0.
Proof. solve_nonhalt 4 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB0LD_1RC0LB_1RD0RE_1RE0RD_1LF1RA_---1LB") c0.
Proof. solve_nonhalt 4 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB1LE_1LC1RE_1RB1LD_0LE---_0LF1LF_0LB0RA") c0.
Proof. solve_nonhalt 5 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB1LF_0LC0RE_1LA1RD_0LB1LB_1RC1LD_0LD---") c0.
Proof. solve_nonhalt 5 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB1LC_1LA1RD_0LD---_0LE1LF_0LB0RA_0LB0LE") c0.
Proof. solve_nonhalt 5 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB1LE_0LC0RD_1LA0RD_1RC1LF_0LF---_0LB1LB") c0.
Proof. solve_nonhalt 5 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB1LE_1LC0RA_1RB1LD_0LE---_0LF1LF_0LB0RA") c0.
Proof. solve_nonhalt 5 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0RA_1LC1RF_---1LD_1RE0LD_1RA0RB_1RD0LA") c0.
Proof. solve_nonhalt 4 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0LC_1LC0LB_0RD0LB_0RA1RE_1RD0RF_0RC---") c0.
Proof. solve_nonhalt 15 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB0RA_1LC0LB_0RD0LB_0RA1RE_1RD0RF_0RC---") c0.
Proof. solve_nonhalt 15 3200 0%N (10^8)%N. Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB0RC_1RC0RB_1LD1RF_---1LE_1RA0LE_1RE0LB") c0.
Proof. solve_nonhalt 4 3200 0%N (10^8)%N. Time Qed.

