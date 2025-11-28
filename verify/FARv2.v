From BusyCoq Require Import CTL62.

Ltac solve_cert ::= Nsolve_cert.

Lemma nonhalt1: ~halts (TM_from_str "1LB1LE_1RC0LD_0LA0RD_1RB1RF_0LD1LF_0LC---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 0 4 0 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1RA_1LC0RF_---0LD_0LE1LC_1LA0RA_0RA1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 15 3200 2 13 1 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB0LD_1RC0RE_0RD---_1LE1LA_1RA0RF_0RE1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 4 3200 1 3 2 0). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LA_0LC0RE_0LD1LC_1LA0RF_0RB1RD_0RA---") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 20 3200 2 3 16 0). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0RD_1LC1LE_1RA0LB_1RE---_1RF0RC_1RA1RE") c0.
Proof. solve_cert (CPS_LRU_FAR 60000 30000 12 3200 1 15 0 0). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1LB0LD_0LC---_1RD1RE_1LE0LF_1LA0RC_0LD1RC") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 4 3200 2 5 1 0). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1LB1LC_1RC0RF_1RD0LA_1RE0RB_0RA---_0RB1LA") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 1 3200 2 4 12 0). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0LE_0LC0RE_1LA1LD_0LE1LF_1RA0RE_0LB---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 12 3200 0 12 0 0). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB---_1RC0RF_1RD1RB_1RE0RA_1LF1LB_1RD0LE") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 12 3200 2 2 16 0). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB---_1RC1LD_1LD1RF_0LE0LD_1RE0RC_1RA0RC") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 8 3200 2 5 1 0). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB0RE_1RC1RA_1RD0RF_1LE1LA_1RC0LD_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 2 14 0 0). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0RA_1RC0LA_0LD0RA_1LB1LE_0LA1LF_0LC---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 1 10 1 0). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB0RF_1RC0LE_1RD0RA_0RE---_1LA1LB_0RA1LE") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 5 3200 2 2 4 0). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB1RE_1LC0RD_1RB1LA_0RC1RA_1RF0LE_1LC---") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB0LB_1RC0LA_0RD1LA_0RF0RE_1RF---_0RA1RE") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 3 3200 2 6 3 0). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1LB1LE_1RC0LA_1RA0RD_1RE---_1RF0RB_1RC1RE") c0.
Proof. solve_cert (CPS_LRU_FAR 60000 30000 12 3200 1 15 0 0). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB0LE_0RC1LE_0RD0RF_0RE1RF_1LA0LA_1RD---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 3 3200 2 6 3 0). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1LB0RC_1RA1LD_0RB1RD_1RA1RE_0RF0LE_0LD---") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1LB0RF_0LC---_0LD0RA_1LE0LC_0RA0LA_1RE1RF") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 2 3200 2 3 8 0). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1LB0RB_1RA0RC_1RB0LD_1LC1LE_0LC1LF_1LB---") c0.
Proof. solve_cert (CPS_LRU_FAR 60000 30000 4 3200 2 3 1 0). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1LB0RC_1RA1LD_0RB1RD_1RA1RE_0RF0LE_0LB---") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB1RA_0RC0LC_1LD0RA_0LE---_0LF0RC_1LB0LE") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 2 3200 2 2 12 0). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB0RE_1LC0RB_0LA0LD_1RA1LC_0RF0RC_---0RD") c0.
Proof. solve_cert (CPS_LRU_FAR 4000000 1000000 3 3200 2 2 0 0). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1LB1RA_1LC0LE_1RD1LB_0LB0RA_1LF0RB_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 7 3200 2 6 4 0). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LD_1LC1RE_1LA1RC_1LB1LD_---1RF_0RA0RF") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 24 3200 2 6 16 0). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB1LF_0RC1RC_0RD1RB_1RE0RE_1LA---_0LA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 3 3200 2 6 4 0). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB0RC_1RC0LB_0RF0RD_0RE---_1RA1RE_0LA1LD") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 6 3200 2 4 4 0). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1LB0RA_1RC0LD_1LA0RD_0LE0LB_0RC1LF_0LC---") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 6 3200 2 6 3 0). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1LB0RD_1LC0RB_1RA0LD_0LE0LC_0RA1LF_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 6 3200 2 6 3 0). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB0LD_1LC0RD_1LA0RC_0LE0RC_0RB1LF_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 6 3200 2 6 3 0). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1LB0RD_1LC0RB_1RA0LD_0LE0RB_0RA1LF_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 600000 300000 6 3200 2 6 3 0). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0LE_1RC1RD_0RD---_1LA0RA_0LF1LE_0LA0RC") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 4 3200 2 3 4 0). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1LB0RA_1LC0RF_1RD0LC_0RA1RE_---1RB_0RC0LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 23 3200 2 6 1 0). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0LA_0RC1RE_1LD0RC_1LA0RF_---1RD_0RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 23 3200 2 6 1 0). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0LA_0RC1RE_1LD0RC_1LA0RF_---1RD_0RA0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 23 3200 2 6 1 0). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1LB0RA_1LC0RF_1RD0LC_0RA1RE_---1RB_0RC1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 23 3200 2 6 1 0). Time Qed.

