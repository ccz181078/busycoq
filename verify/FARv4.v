From BusyCoq Require Import CTL62.

Lemma nonhalt1: ~halts (TM_from_str "1LB1LD_1RC1RA_1LA0RB_1RB0LE_0LF1LA_---1RD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 1 6 1 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1LB0RC_1LC0RD_1RA0LB_0LA0RE_1LA1RF_1RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 3 3 12 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1LB0RD_0LC1LE_1RD---_1RA0RA_1RE0LF_0RF1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LE_1LC0RE_0LD1LC_0RA0LE_1LA1RF_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB---_1LC0RF_1LF0RD_0LB0RE_1LB1RA_1RB0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 3 3 24 0). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LA1RE_1RF0RA_---1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1LB1RD_1RC0LA_1LE1RD_0RE---_1RF0LB_1LE0RC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD0LF_0RA0LF_0RE1RD_1LC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD1LC_0RA0LF_0RE1RD_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB---_1RC0RC_1LD0RB_0LA1LE_1RE0LF_1RB1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 1 5 0 0). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1LB0RF_1LC1LD_0RD---_1RD0LE_1RF1LB_1RA0RA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB0LC_1LC1RE_1RD0LB_1LA0RB_0RF---_1RD0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1LB0RD_1LC0LC_1RA0LD_1LC1RE_0RF---_1RA0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 2 3 24 0). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1LB1RD_1LC1LE_0RA1LA_---1RE_1RC0RF_1RE0LA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 2 3200 2 4 4 0). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB0RD_0LC1LE_1RD---_1RA0RA_1RE0LF_0RB1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB---_1LC1RE_1RD0LB_1LF0RB_0RF---_1RD0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1LB---_1LC0RD_1RB0LF_1LF1RE_0RC---_1RB0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1LB0RD_1LC0LF_1RA0LC_1LF1RE_0RC---_1RA0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD1RB_1RA0LE_1LD1RF_0RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB1RC_1LA0RE_1LE1LD_0LA0LC_0LF0RB_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 0 11 1 0). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1LB0RC_0LC0LD_1LD1RE_1RA0LC_0RF---_1RA0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1LB---_1LC1RE_1RD0LB_1LF0RB_0RF---_1RD0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1LB0LC_1LC1RE_1RD0LB_1LA0RB_0RF---_1RD0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB0RC_1RC0RA_0LD1RB_1RF0LE_1LD1RE_---1RA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 6 3200 2 3 12 0). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LC_1LC1RE_1RD0LB_1LA0RB_0RF---_1RD0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB1LC_1LC0RE_0LD1LD_0RA0LF_0RE1RD_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB---_1RC0LF_0RD1RB_0RE0LB_1LF0RC_0LA1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 8 3200 2 14 0 0). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB1LA_1LC0RE_0LD1LC_0RA0LE_1LD1RF_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1LB0RD_1LC0LF_1RA0LF_1LF1RE_0RC---_1RA0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB---_1LC1RD_1LD0LC_0RE1LC_0RA0RF_1LA0RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB0RB_1LC0RA_0LF1LD_1RD0LE_1RA1LC_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB0RA_1RC0RE_0LD1RA_0LA1LD_1RF0LC_0LE---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB---_1RC0RC_1LD0RB_0LA1LE_1RE0LF_0RF1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1LB0RE_1RC0LA_---1RD_1LD0LA_1RA0RF_0LD1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0RB_1LC0RA_1LF1LD_1RD0LE_1RA1LC_0RD---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 0 2 1 0). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1LB---_1RC0LF_0RD1RB_0RE0LB_1LF0RC_0LA0RF") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB0LE_1RC1LD_1LB0RE_0LA1RC_1LA1RF_0RB---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1LB0RF_1RC0RA_1RE1RD_0RB1LE_1LD0LE_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB0LD_1RC0RA_0RD1LD_1LE1RF_1LC1LB_---1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB---_1RC0RC_1LD0RB_0LA1LE_1RE0LF_0RD1LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB0LD_0RC1RB_0LD0RE_1RE1LE_1LA0RF_---0LA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB0RB_1LC0RA_0LF1LD_1RD0LE_0RE1LC_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB---_1LC1RD_1LD0LC_0RE1LC_1RA0RF_1LA0RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB1LC_1LA0RE_0LD---_0RA0LF_0RE1RD_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB1RE_1RC0RA_0LD1RB_0LA1LD_0RF0LB_---0LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB0LD_1RC1LA_1LB0RE_0RB0LF_0RE1RD_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1LB0RD_1LC0LC_1RA0LD_1LC1RE_0RF---_1RA0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB0RB_1LC0RA_0LF1LD_1RD0LE_0RC1LC_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 2 4 0 0). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB0RD_1LC1RB_1RD0LB_0LA1RE_1RF0RA_---0RA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1LB0RD_0LC1LE_1RD---_1RA0RA_1RE0LF_1RD1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1LB0RC_0LC0LD_1LD1RE_1RA0LC_0RF---_1RA0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB1LC_1LA0LC_0LD1RE_0RA0LF_0RE1RD_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB0LC_1LC1RE_1RD0LB_1LA0RB_0RF---_1RD0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB0RF_0RC1LC_1LD1RE_1LB1LA_---1RA_1RA0LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1LB1RD_1LC1LF_0RA0LF_0RD0RE_1RC---_0LB1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 3 24 2). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB0LD_0RC1RB_0LD0RE_1RE1LE_1LA1RF_---0LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 2 3200 2 3 8 0). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB0LF_1LC1RD_1LF1LA_---0RE_1RA0RC_0LE0RE") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB0RE_1RC0RA_0LD1RB_0LA1LD_0RF1RB_---0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB0LD_0RC1RB_0LD0RE_1RE1LE_1LA1RF_---0RC") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1LB1LC_0RC---_1RC0LD_1RE1LA_1RF0RF_1LA0RE") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB0LF_1LC1RB_1LA1RD_---0RE_0LF0RC_1RC1LC") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB1RE_1RC0RA_0LD1RB_0LA1LD_1RF0LB_---0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB0RC_1RC0RA_0LD1RB_1RE1LD_---0RF_1LB1LC") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 6 3200 1 2 1 0). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB---_1RC1RD_1LB0RF_1LF1LE_0LB0LD_0LA0RC") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 1 6 1 0). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB0LF_0RC---_1RD1LF_0LE1RC_0LA1LD_0LB0RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 4 2 24 2). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1LB1LA_1LC0RE_0LD0RC_1LE1LF_1RC1RE_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1LB0RE_0LC1LA_1RC0RD_0LA0RF_0RA1RE_---0LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 4 3200 2 3 3 0). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB0LE_0RC1RA_0RD0LA_1LE0RB_0LF1LA_1LA---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB---_1RC0LF_0RD1RB_0RE0LB_1LF0RC_1LA1LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB1LD_1LB1RC_1RE0RD_1LC1LF_0RB0RE_0LA---") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 0 2 1 0). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1LB0RE_0LC1LD_1LD---_1RE0LB_0RF1RD_0RA0LD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB0LE_0RC1RA_0RD0LA_1LE0RB_1LF1LA_1RA---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB0LE_0RC1RA_0RD0LA_1LE0RB_0LF0RE_1LA---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1LB0RE_1LC1LD_1RD---_1RE0LB_0RF1RD_0RA0LD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1LB1LC_1RC---_1RD0LA_0RE1RC_0RF0LC_1LA0RD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1LB0RE_0LC0RB_1LD---_1RE0LB_0RF1RD_0RA0LD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 4 8 0). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1RB1RD_1LC0RA_0LF1LD_1LA1LE_1RA0LC_---1RE") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 0 7 1 0). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1LB0RD_1RC0LA_1LA0RB_0LC0RE_1LC1RF_1RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 3 3 12 0). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1LB0RC_1RA1RE_0LD0RA_1RB---_1LC1LF_0LB0LE") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 12 3200 0 10 2 0). Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1RB---_1RC1LD_0LB0RE_0LA1RE_0RD0LF_1LC1LE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 100000 10000 0 0 0 1 2 6 24 0). Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1LB1LF_0LC0RF_1RB1LD_0LE1RF_1RC---_0RD0LA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 20000 10000 0 0 0 1 2 6 24 0). Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1RB0LC_1LC0RD_1LA1RC_1RE1RC_---0RF_0RB0RB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 3 8 0). Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1LB1RF_1LC---_1LD0RF_1LE0LC_1RC1LB_1RC0RA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 8 3200 2 3 8 0). Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1LB1RA_0LC0RF_1RC1RD_0LE1RB_1LB1LE_---0RA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 4 3200 0 16 0 0). Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1LB1RE_1LC1LC_1RD0RF_1RE1RD_1LF0RC_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 4 3200 2 6 8 0). Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1LB1LD_1RC0RE_0LA1RB_1RF0LE_0LD1LC_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 40000 10000 0 0 0 1 2 4 12 2). Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1RB0LE_0LC0RF_---1RD_1LA1RE_1LA1LB_1RD0RD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 3 4 24 2). Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1LB0RD_0RC0LE_---1RD_1RA0RD_1RB1LF_0LE0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 12 1). Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB0LD_0LC0LE_---1LD_1LA0LD_1LB1RF_0RE0RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 12 1). Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1LB1LC_0RC0LE_---1RD_1RA0RD_1RB1LF_0LE0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 12 1). Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1RB1RC_0LC0LE_---1LD_1LA0LD_1LB1RF_0RE0RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 12 1). Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1RB1LB_1RC0LB_1LA0RD_---0RE_0RF0LF_1LA1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 12 12 0). Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1RB1LB_1LC1LF_1RD1LC_0LA1RE_1RC0RD_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 8 3200 2 5 3 0). Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1RB0RB_1LC1RD_1RE0LD_1LC1LE_1LF0RA_---0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 3 4 24 2). Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1RB0LD_0LC0RE_---1RD_1LA1LB_1RF0RF_1LA1RD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 3 4 24 2). Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE0RF_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 2 3200 2 5 3 0). Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1RB1LC_1LA0RD_0LB0LF_1RE0RE_1RB0RB_1LC---") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 18 3200 2 6 16 0). Time Qed.

