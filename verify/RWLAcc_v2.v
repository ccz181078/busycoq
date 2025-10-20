From BusyCoq Require Import RWLAcc62_BigUint.

Ltac solve_nonhalt' bsz bmaxT mnc T :=
  eapply (decide_nonhalt_spec _ bsz bmaxT true (of_nat (N.to_nat mnc)) T);
  native_cast_no_check (eq_refl true). 

Ltac solve_nonhalt bsz := solve_nonhalt' bsz 3200 0%N (10^8)%N.

Lemma nonhalt1: ~halts (TM_from_str "1RB0LB_0RC---_0RD0LE_0RE0LA_1LF0LA_1LC0LF") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB---_0LC0RB_1RA1RD_1LE1RE_0RC0LF_1LB1LD") c0.
Proof. solve_nonhalt 3. Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RB---") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_0LE---") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0LD_1RC0LE_1LA1LC_---1LA_1RF0LE_1RF1RB") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0LE_0RC0RA_0RD0RC_1LE0RF_1LA0LD_0RE---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0LE_1RC1LE_1RD---_1RE0RF_1LA0LF_0LB0RC") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0RA_0LC0RF_0LF0RD_1LE0RE_0LB---_1RA0RD") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0RD_1LC0LD_0LD0LB_0LE0RF_1RF1LB_1RA---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0RD_1LC1LF_0RD1LD_1RE0LD_1RA1RE_---1LB") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB0RE_1LC0LE_1RD0LB_1RF1LB_0LD0RF_1RA---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LD_1RA0LF_0LA---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB1LB_0LC0RD_1LF1LA_1RE1RA_0RC0LE_1LE---") c0.
Proof. solve_nonhalt 3. Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB---_1LC0RD_1LB1LD_1LE0RB_0LF1LA_0RA0LE") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB---_1LC0RD_1LC1LD_1LE0RB_0LF1LA_0RA0LE") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB1LC_1LA0RE_1LD0LF_1RE1LB_0RC1RB_1LC---") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1LD_1RC0LD_1RD0RE_1LB0LE_0LA0RF_1RC---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB1LD_1RC---_1RD0RF_1LE0LF_0LF0LD_0LA0RB") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB1LD_1RC---_1RD0RF_1LE0LF_1RA0LD_0LA0RB") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB1LD_1RC---_1RD0RF_1LE0LF_1RC0LD_0LA0RB") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB1LE_1RC---_0RD1RA_1LD1LE_1RF0LE_0RC0RF") c0.
Proof. solve_nonhalt 1%nat. Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1RA_1RC0RE_1LD1LF_0RE1LE_1RA0LE_---1LC") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB1RE_1LC1RA_1RC0LD_0LC0RE_1RF---_1RA0RA") c0.
Proof. solve_nonhalt 6. Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB0RD_1RC1RA_1LD0RE_1RF0LE_1LA1LC_---0RB") c0.
Proof. solve_nonhalt' 78 10000 2%N (10^8)%N. Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LE_1LC0RE_---0LD_1LA1LF_1RF1RA_1LD0LB") c0.
Proof. solve_nonhalt' 78 10000 2%N (10^8)%N. Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB0RF_1LC0RA_0RD0LB_1LA1LE_0LC---_1RA1RE") c0.
Proof. solve_nonhalt' 304 100000 2%N (10^8)%N. Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LD_0RE0LF_1LB1RA_1LC---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LD_0RE0LF_1LF1RA_1LC---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0RD_1LC0LD_1RA0LB_0LE0RF_1RF1LB_1RA---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RB0LC_0LF0RA_1RA1LC") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB---_1RC0RE_1LD0LE_1RB0LC_0LF0RA_1RD1LC") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0RD_1LC0LD_1RA0LB_0LE0RF_1RC1LB_1RA---") c0.
Proof. solve_nonhalt 2. Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB1RC_1LB0RA_1RD0LD_1LE1LA_---1LF_1LC0LC") c0.
Proof. solve_nonhalt 30. Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0LC_1RC0RF_1LD0RE_1LE1LD_0RB0LA_---1RE") c0.
Proof. solve_nonhalt 6. Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0RE_1LC0RD_1LD1LC_0RA0LF_---1RD_1RA0LB") c0.
Proof. solve_nonhalt 6. Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB0RA_0LC0RA_0LE1LD_1LC0LF_1LA0RB_0LB---") c0.
Proof. solve_nonhalt 10. Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB0RA_0LC0RA_0LE1LD_1LC0LF_1LA0LE_0LB---") c0.
Proof. solve_nonhalt 10. Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB---_1RC1LD_1RD1RF_1LB0LE_0RE0LB_0RA0RF") c0.
Proof. solve_nonhalt 10. Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB0RA_0LC0RD_1LD1LB_1RA1LE_1LF---_1LB0LB") c0.
Proof. solve_nonhalt 9. Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB---_1RC0RC_0RD0LE_1RE1RC_1LF1RA_1LC0LF") c0.
Proof. solve_nonhalt 9. Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB1LE_1RC0RB_0LD0RA_1LA1LC_1LF---_1LC0LC") c0.
Proof. solve_nonhalt 9. Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB1RF_1LC0RD_1RE0RD_0RC0LE_1LB0RA_0RE---") c0.
Proof. solve_nonhalt 24. Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB0LE_1LC0LE_1RA0LD_1LA1LF_0LB0RC_0LC---") c0.
Proof. solve_nonhalt 24. Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB0LF_0RC0RF_1RD---_1LE0LB_1LA0LD_1RA0RE") c0.
Proof. solve_nonhalt 24. Time Qed.

