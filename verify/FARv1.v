From BusyCoq Require Import CTL62.

Ltac solve_cert ::= Nsolve_cert.

Lemma nonhalt1: ~halts (TM_from_str "1RB1LC_0RC0RD_1LA1LE_0LC0RB_0LF0LE_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 2 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB1LA_1RC0LF_0RD0RA_1RE1RA_1LB---_1LA1LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB1LA_1RC0LF_0RD0RA_1RE1RA_0RF---_1LA1LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LE_0RC0RF_1RD1RF_1LA---_1LF1LA_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB0LE_0RC0RF_1RD1RF_0RE---_1LF1LA_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB1RD_0RC---_1LD1LE_1RE1LD_1RF0LC_0RA0RD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB1RE_1LC---_1RF0LD_1LE1LC_1RC1LE_0RA0RE") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0LC_1RC0RF_1LA1LD_1RE0RA_1RB1RD_1RD---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 6 3200 2 2 6 0). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB0RF_1LC1RE_1LD1LC_1RB0LC_---0RA_0LF1RB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0LB_1RC0LE_1RD---_0RE1RF_1LA1RE_0RA0RC") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 10 3200 2 4 8 0). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1LB1LC_1RC1LB_1RD0LA_0RE0RB_1RF1RB_0RA---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB---_1RC0LF_0RE0RD_1RB1LD_1RA1RD_1LD1LB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1LB1LE_1RC---_1LE1RD_1LA0RC_1LF0LD_1LC0RD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 6 3200 2 6 4 0). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1LB1RD_1LC1LB_1RA0LB_---0RE_1RA0RF_0LF1RA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB1RE_0RC1LD_1LD1RB_0LA1RA_1RF0LF_---0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 3 3200 1 3 2 0). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1LB1LD_1LC0RA_1LD0LB_1RE0RF_---1RD_1RB1RF") c0.
Proof. solve_cert (RWL_mod_FAR 1000000 1000000 2 3200 2 1 6 0). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1LB1RB_1LC0RA_0RD1LE_1RB1RD_1LF0LB_---1RD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 18 3200 2 1 16 0). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1LB1RD_1RC0LA_1LC1LA_0RF0RE_1RA0RB_---1RC") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 8 3200 2 2 0 0). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1LB0LF_0LC1LE_1LD---_1LE0RD_1RA0LA_1RD1RF") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 8 3200 2 3 6 0). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1LB0LE_1RC0LA_1RD1RB_0RE0RF_1LF1LB_0RB---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 1 4 1 0). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1LB1RA_1RC0LD_0RD1RC_1LA1RE_0RF0RB_---0RA") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1LB1RE_1LC1RB_1RD0LA_0RA1RD_0RF0RC_---0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1LB1RE_1RC0LA_---1RD_1RA1RA_0RD0RF_0RA0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 4 3200 1 3 2 0). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1LB1RB_1LC0RA_0RD1LF_1LE1RD_---1RA_1LD0LB") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 18 3200 2 1 16 0). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1LB1LC_1RC0LA_1LA0RD_0RB0RE_0RF1RD_---1LA") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 10 3200 2 2 3 0). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1LB1LF_0RC0LA_0RD1RB_0LE0RD_1LA---_1RC0LD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 5 3200 2 2 3 0). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB0RD_0LC---_1LD0LF_1RE1LC_0RA1RE_0RA0LA") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 18 3200 1 15 0 0). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1LB1RE_0RC1LA_0LE0RD_1RB1RA_1RA0LF_---0LC") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 6 3200 2 3 4 0). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1LB1RA_1RC0LC_1RD0LA_1RE---_0RA1RF_0RB0RD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 20 3200 2 4 6 0). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1LB0LE_1RC0LA_1RD1RB_0RE0RF_1LF0RE_0RB---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 12 3200 2 4 0 0). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1LB0RD_0RC0RF_0RD1RB_1LE0LE_0LA---_0RB0LD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 4 3200 2 2 4 0). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1LB1RB_1LC---_1RD0LD_1LF0RE_0RD0RC_0LA1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 22 3200 1 2 0 0). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB0LC_1LA1RF_1LD1RB_0LE0RD_1LB---_1LD0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 1 4 1 0). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0LF_1RC1RA_0RD0RE_1LE1LA_0RA---_1LA0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 1 4 1 0). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0LF_1RC1RA_0RD0RE_1LE0RD_0RA---_1LA0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 1 4 1 0). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB0LB_1LC0LD_0LF1LA_1RE1RD_1LA0RE_1LE---") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 4 3200 2 3 12 0). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB0LD_1RC---_0RD1RF_1LE1RD_1RA0LA_0RE0RB") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 20 3200 2 4 8 0). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB---_1RC1RE_1LD0LD_1RF1LE_0RC0LC_0RB0RA") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 6 3200 1 3 2 0). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB1RA_1LC0RB_1RD0LD_1LE0LA_0LF1LC_1LB---") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 8 3200 2 2 8 0). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RC_1RE0LE_1RA0LC_0RD0RA") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 20 3200 2 4 8 0). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB1RE_0RC0RD_1LD1LE_0RE---_1RA0LF_1LE0LC") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 24 3200 1 4 1 0). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB1LE_0RC0RF_1RD1RE_1LA0LA_0RD0LD_1RC---") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 6 3200 1 3 2 0). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB---_0RC1RF_1LD1RC_0LE0LE_1RA0LC_0RD0RA") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 20 3200 2 4 8 0). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB0LE_0RC0RB_1LD0LA_1LC---_0RF1LF_1LA1RF") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 4 3200 2 2 0 0). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB1RA_1LC0RE_1LF1LD_1LE0LA_0RA0LC_---1LC") c0.
Proof. solve_cert (CPS_LRU_FAR 200000 100000 8 3200 1 13 2 0). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB1LF_0RC0LC_1RD1LE_1LB0RB_0LF---_0LA0LD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 6 3200 2 6 4 0). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB1LE_0RC0RF_1RD0RC_1LA0LD_1LD---_1LF1RB") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 4 3200 2 2 4 0). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB1LF_0RC0RE_1LD1RA_1LE1RD_0LA0LD_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 5 3200 2 2 3 0). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB1RE_0RC0RD_1LD0RC_0RE---_1RA0LF_1LE0LC") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 12 3200 1 5 2 0). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1LB0LA_1RC1LE_1RD0RC_1RA1RF_1RC0LA_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 24 3200 2 3 4 0). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1LB0LD_1RC0LF_1RD0RC_1LA0LE_1LE0RB_1LC---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 10 3200 2 4 0 0). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1LB1RA_1RA1LC_1LD0LB_1RE0RD_---1RF_1LA0RF") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 2 3200 2 12 2 0). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1LB1RA_1LC1LB_1RD1LF_1LA0RE_0RD1RD_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 2 6 0). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1LB1LA_1RC1LF_1LE0RD_0RC1RC_1LA1RE_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 2 6 0). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1LB1LA_1RC0LB_1RD1RC_1RE0RC_1LF1LE_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 3 3200 2 1 4 0). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB0LA_0RC1RE_0RD0LF_1LE1RA_0LC---_1LC1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 16 3200 2 6 3 0). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB0RA_1LC0LE_1LD0LB_1RA0LF_1LE0RD_1LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 16 3200 2 6 3 0). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB0LB_1LC1RD_---1LA_0RB1RE_1LC1RF_0RD0RA") c0.
Proof. solve_cert (RWL_mod_FAR 4000000 1000000 5 3200 2 2 4 0). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB1LE_1RC0LD_1RD0LA_0RE0RC_1LF1LB_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 1 8 0). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB0LF_0RC0RA_1LD1LE_0LE---_1RA0LB_1RE1LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 1 8 0). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB0LC_1RC0LF_0RD0RB_1LE1LA_0LA---_1RA1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 1 8 0). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB1RC_0RC---_1LD0RE_1LE0RF_0LA0LD_1LC1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 1 8 0). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB0LE_1LC0RC_1RF0LD_1LE---_0LF1LC_1LA0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 1 8 0). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB1RA_1RC0RA_1LD1LC_---0LE_1LF1LE_1RA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 3 3200 2 1 4 0). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1LB0RB_1RC0LE_1LD0RD_1RA0LF_0LA1LD_1LE---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 2 6 0). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1LB0RE_1LC1RB_1LD1LC_1RA1LF_0RA1RA_0LC---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 2 6 0). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1LB0RF_1LC0LA_1RD0RE_---1RC_1RA1RE_1LA1LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 2 3200 2 1 6 0). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB0RE_1RC---_1RD1RA_1RE1RD_0LF1RA_0LA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 2 3200 50 1 16 0). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB---_1RC1RF_1RD1RC_0LE1RF_0LF1LE_1RA0RD") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 2 3200 50 1 16 0). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1LB0RC_1LC0LA_1RA0RD_1RE0LB_0LD1RF_0RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB0RD_1LC0RA_0LD0LB_1RE0LD_0RA1RF_0RB---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 10 24 1). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_0LD1RF_0RB---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 10 24 1). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB0LA_0RC1RF_1RD0RA_1LE0RC_0LA0LD_0RD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1LB1LA_1RC0RD_---1RD_0RE1LE_0LA1RF_0RB1RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1RB0RD_1LC0RA_1LA0LB_1RE0LC_0RA1RF_0RB---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1RB0LC_0LA1RF_1LD0LE_1RE0RA_1LC0RD_0RE---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1LB0RC_1LC0LA_1RA0RD_1RE0LB_0RC1RF_0RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1LB0RE_0LC0LA_1RD0LC_0RE1RF_1RA0RC_0RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1LB0LC_1RC0RD_1LA0RB_1RE0LA_0RB1RF_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 2). Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1LB0LF_1LC1RB_1RD0LA_1LA0RE_0RD0RC_1LD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 9 24 2). Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1LB1RA_1RC0LE_1LE0RD_0RC0RB_1LA0LF_1LC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 9 24 2). Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1LB---_1LC0RF_1LD0LA_1LE1RD_1RB0LC_0RB0RE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 9 24 2). Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1LB0RE_1LC0LF_1LD1RC_1RA0LB_0RA0RD_1LA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 9 24 2). Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1RB0LC_1LC0RF_1LE0LD_1LB---_1LA1RE_0RB0RA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 9 24 2). Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1LB0LF_1LC0RD_1LD0LA_1RB1RE_0RB0LE_1LC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 600000 300000 0 0 0 1 2 8 24 2). Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_1LC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 600000 300000 0 0 0 1 2 8 24 2). Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1LB0LA_1RC0LD_1LA0RD_0LE1RF_0RB1RC_0RC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 2 0 0 1 1 1 24 0). Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1RB1RA_1LC0RD_1RF1LD_0RE1LC_---0LC_1RE0RA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 1 0 0 1 2 1 24 2). Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB0LD_0LC0RE_---1LD_1LE1LA_1RA0LF_1LC1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 18 3200 2 6 12 0). Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1RB0LD_0LC0RE_---1LD_1LE1LA_1RA0LF_1LC1LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 18 3200 2 6 12 0). Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1RB0RC_0RC0RA_1RD1LA_1LE0LB_0LB1LF_0LD---") c0.
Proof. solve_cert (RWL_mod_FAR 200000 100000 16 3200 2 6 8 0). Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1RB0RE_1LC0RA_0LD0LB_0LE0LB_1RA1LF_1RA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 11 3200 2 4 12 0). Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1LB1RE_0RC0LA_1LF1RD_1RE0LD_0RB1RF_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 14 3200 2 4 8 0). Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1LB---_1RC0LB_0RD1RC_1LE1RF_0LF0RB_1RA0LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 5 3200 2 3 6 0). Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1LB0RA_0LC1LB_1RD1LE_0RE0LA_1LF0RD_1RA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 10 3200 2 3 4 0). Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1RB1LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_1RB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 11 3200 2 4 12 0). Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1LB---_0LC0RE_1LD1LF_1RB0LA_1RB1RF_1LC0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 6 3200 2 2 0 0). Time Qed.

Lemma nonhalt98: ~halts (TM_from_str "1LB1LA_0LC0RB_1LD0LD_1LE0LB_1RF1RA_---1RE") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 6 3200 2 6 4 0). Time Qed.

Lemma nonhalt99: ~halts (TM_from_str "1LB1LA_0LC0RB_1LD0LD_1LE0LB_1RE1RF_---1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 6 3200 2 6 4 0). Time Qed.

Lemma nonhalt100: ~halts (TM_from_str "1LB0RE_1LC0LB_1RD0LB_1RA1RE_0RC1RF_0RD---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 6 3200 2 6 3 0). Time Qed.

Lemma nonhalt101: ~halts (TM_from_str "1RB1LF_1LC0RE_1LD1RC_1LA1LD_0RB1RB_0LD---") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 16 3200 2 2 2 0). Time Qed.

Lemma nonhalt102: ~halts (TM_from_str "1RB1LB_1LC0RB_0LF1LD_1LE---_1LF0RA_1RF0LE") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 14 3200 2 5 16 0). Time Qed.

Lemma nonhalt103: ~halts (TM_from_str "1RB---_1RC0RB_0LD1RF_1RB1LE_1LD0LE_1RA0RE") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 10 3200 2 5 8 0). Time Qed.

Lemma nonhalt104: ~halts (TM_from_str "1RB1LD_1RC0RB_0LA0RE_0LC1LA_1LA0RF_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 15 3200 2 3 8 0). Time Qed.

Lemma nonhalt105: ~halts (TM_from_str "1LB0LD_0LC0LA_1LD1RC_1RE1LA_0RF1LC_---0RE") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 15 3200 2 3 8 0). Time Qed.

Lemma nonhalt106: ~halts (TM_from_str "1RB1LA_1LC0LB_1RD1LD_1LA0RE_1RF0RE_0RC---") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 16 3200 2 4 0 0). Time Qed.

Lemma nonhalt107: ~halts (TM_from_str "1RB0RF_1RC---_1RD0RC_0LE1RA_1RC1LF_1LE0LF") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 10 3200 2 5 8 0). Time Qed.

Lemma nonhalt108: ~halts (TM_from_str "1LB0LD_0LC1LE_1RD1LF_0RE0RD_0LA1RC_---1LA") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 24 3200 2 3 12 0). Time Qed.

Lemma nonhalt109: ~halts (TM_from_str "1RB0RA_0LC0RE_1RA1LD_0LB1LC_1LC0RF_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 15 3200 2 3 8 0). Time Qed.

Lemma nonhalt110: ~halts (TM_from_str "1RB1LE_1RC0RB_1LD0RC_1LF0LA_1LC1RD_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 12 7 0). Time Qed.

Lemma nonhalt111: ~halts (TM_from_str "1RB1LE_1RC1RE_1LD0RC_1LF0LA_1LC1RD_0LB---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 8 3200 2 12 7 0). Time Qed.

Lemma nonhalt112: ~halts (TM_from_str "1RB1LB_1LC0RE_0LD0RA_1LE1LC_1RC1LF_0LC---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 12 3200 2 1 14 0). Time Qed.

Lemma nonhalt113: ~halts (TM_from_str "1LB1LC_1RC1LF_0LA0RD_1RE1LE_1LC0RB_0LC---") c0.
Proof. solve_cert (RWL_mod_FAR 2000000 1000000 12 3200 2 1 14 0). Time Qed.

Lemma nonhalt114: ~halts (TM_from_str "1RB1LD_1RC1RB_1LA0RF_---0LE_0LC1LE_1RB1RE") c0.
Proof. solve_cert (RWL_mod_FAR 18000000 3000000 6 3200 2 1 4 0). Time Qed.

Lemma nonhalt115: ~halts (TM_from_str "1LB0RF_1RC1LD_1RA1RC_---0LE_0LA1LE_1RC1RE") c0.
Proof. solve_cert (RWL_mod_FAR 18000000 3000000 6 3200 2 1 4 0). Time Qed.

Lemma nonhalt116: ~halts (TM_from_str "1RB0RF_0LC1RA_0LD1LD_1RE1LC_0RB0RC_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 6 3200 2 2 4 0). Time Qed.

Lemma nonhalt117: ~halts (TM_from_str "1LB---_1LC0RD_1LD0LF_1RB1RE_0RB0LE_1LB0LA") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 6 3200 2 2 8 0). Time Qed.

Lemma nonhalt118: ~halts (TM_from_str "1RB0RA_0LC1RA_1RC1LD_0LC1LE_1LF0LB_---0LA") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 16 3200 2 13 1 0). Time Qed.

Lemma nonhalt119: ~halts (TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB1LF_0RB0LE_0RC---") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 6 3200 2 2 8 0). Time Qed.

Lemma nonhalt120: ~halts (TM_from_str "1RB1LB_0RC0LB_0LD0RA_1LE---_1LF1LC_0LA1LA") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 2 3200 2 1 16 0). Time Qed.

Lemma nonhalt121: ~halts (TM_from_str "1LB0RD_1LC0LE_0RA0LC_1RA1RD_0LF1LA_---1LC") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 15 3200 2 1 3 0). Time Qed.

Lemma nonhalt122: ~halts (TM_from_str "1RB0RF_1RC---_1RD1LF_1RE0RD_0LC1RA_1LC0LF") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 1 3200 23 0 0 0). Time Qed.

Lemma nonhalt123: ~halts (TM_from_str "1RB1LD_1RC0RB_0LA1RE_1LA0LD_1RF0RD_1RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 1 3200 23 0 0 0). Time Qed.

Lemma nonhalt124: ~halts (TM_from_str "1RB1LD_1RC0RB_0LA1RE_1LA0LD_1RF0RD_0RC---") c0.
Proof. solve_cert (CPS_LRU_FAR 6000000 3000000 1 3200 24 0 0 0). Time Qed.

Lemma nonhalt125: ~halts (TM_from_str "1RB1LA_0RC0LF_0RD---_1RE1RD_1LB1RA_0LD0LA") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 1 3200 24 0 0 0). Time Qed.

Lemma nonhalt126: ~halts (TM_from_str "1RB0RB_1LC0LE_0RF1LD_1RA0LB_1RA0RD_---0RC") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 1 3200 5 0 20 0). Time Qed.

Lemma nonhalt127: ~halts (TM_from_str "1RB0RB_1LC1RA_0LA1RD_1LA1LE_1LF1LD_---0LC") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 6 3200 2 4 6 0). Time Qed.

Lemma nonhalt128: ~halts (TM_from_str "1RB1RD_1LC1LE_1RA0LB_1RE---_1RF0LC_1RC0RF") c0.
Proof. solve_cert (RWL_mod_FAR 6000000 3000000 4 3200 2 3 32 0). Time Qed.

Lemma nonhalt129: ~halts (TM_from_str "1RB1LB_1LC1RE_0RD0LB_0LB1RA_1LA0RF_---0RC") c0.
Proof. solve_cert (CPS_LRU_FAR 1200000 600000 4 3200 3 3 1 0). Time Qed.

Lemma nonhalt130: ~halts (TM_from_str "1RB0LD_0RC1RF_1RD0RA_1LE1RB_1LC0LE_1RC---") c0.
Proof. solve_cert (CPS_LRU_FAR 12000000 4000000 24 3200 4 2 1 0). Time Qed.

Lemma nonhalt131: ~halts (TM_from_str "1LB0RD_1RC1LC_1LE1RA_---0RE_0RF0LC_0LC1RB") c0.
Proof. solve_cert (CPS_LRU_FAR 1200000 600000 4 3200 3 3 1 0). Time Qed.

Lemma nonhalt132: ~halts (TM_from_str "1LB1RE_0RC0LA_0LA1RD_1RA1LA_1LD0RF_---0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 1200000 600000 4 3200 3 3 1 0). Time Qed.

Lemma nonhalt133: ~halts (TM_from_str "1LB0RA_1LC1LA_0RD1RA_1RF1LE_0LD0LE_0RC---") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 4 3200 4 3 0 0). Time Qed.

Lemma nonhalt134: ~halts (TM_from_str "1RB---_1RC1RE_0RD0RF_0RE0RB_0LF0LA_1LE0LB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000000 1000000 24 3200 4 3 1 0). Time Qed.

Lemma nonhalt135: ~halts (TM_from_str "1RB1RE_1LC0LC_1RD1LB_0RB1LA_1RF1RA_---0RD") c0.
Proof. solve_cert (CPS_LRU_FAR 600000 300000 6 3200 6 2 0 0). Time Qed.

Lemma nonhalt136: ~halts (TM_from_str "1RB1RD_1RC0RA_1LD0LE_1RF0RC_1LC0RE_---1RB") c0.
Proof. solve_cert (CPS_LRU_FAR 100000000 5000000 4 3200 3 3 2 0). Time Qed.

Lemma nonhalt137: ~halts (TM_from_str "1RB1RC_1LC0RF_1LD0RA_1RE0LB_---1RA_1RE1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 100000000 10000000 4 3200 2 2 4 0). Time Qed.

Lemma nonhalt138: ~halts (TM_from_str "1LB0RF_1RC0LB_0RD1RA_0LA1RE_0RA1RC_1RA---") c0.
Proof. solve_cert (RWL_mod_FAR 20000000 10000000 22 3200 2 4 3 0). Time Qed.

Lemma nonhalt139: ~halts (TM_from_str "1RB0LA_0RC---_1RD1RE_1LA1LD_1RD0RF_0RC1RC") c0.
Proof. solve_cert (RWL_mod_FAR 20000000 10000000 6 3200 2 3 8 0). Time Qed.

Lemma nonhalt140: ~halts (TM_from_str "1RB1RF_1LC1LB_---0LD_1RE0LD_0RA1RA_0LE0RE") c0.
Proof. solve_cert (RWL_mod_FAR 20000000 10000000 6 3200 2 3 8 0). Time Qed.

