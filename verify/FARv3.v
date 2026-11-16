From BusyCoq Require Import CTL62.

Lemma nonhalt1: ~halts (TM_from_str "1LB1RE_1RC0LF_---0RD_0RE0RE_1RA1RB_1LA1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1LB---_0RC0RD_1RE0LD_1LC1LE_0LF0RB_1RC0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 4 3200 2 1 16 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB0RA_1RB0LF_0LA---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 7 0 0). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LE_0LC0RF_1RA0LD_0LE---_1LA1LB_0RA0RE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 4 8 0). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB1RE_1LC0RF_1RE0LD_1LC1RB_---1RA_1RA0RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 3 12 0). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RF_0RE1RA_1LC---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0LD_1RC1LB_1LA0RE_1LF1LA_1RB1RE_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA0RF_1LA1LD_0RC0RB_---0LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_1LE0RB_---0LA_1LE1RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1RE_---1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1LB---_0RC0RD_1RE0LD_1LC1LE_0LF0RB_0RB0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 2 8 0). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1RA_------") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB0LC_1LC0RD_0LC1LA_0RD1RE_1RF0RE_1LC---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 2 3200 0 3 1 0). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1LB---_1LC0RD_1RB0LF_0RD1RE_0RA0RE_0LF1LC") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 2 3200 0 3 1 0). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1LB---_1RC0RE_0RC1RD_1RE0RD_1LF---_0LF0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1LB0LF_1RC1LB_0LE0RD_1RB1RD_---0LA_1LE1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1LB0RC_0LC0LE_1RD1RC_1RA1LD_0LF1LB_---1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 4 0). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1LB---_0RC1RF_1RE0LD_1LC1LE_0LF0RB_0RB0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 3 0). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB0RE_0LC1RB_---1LD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RA_1RB0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB1LA_0LC0RE_0LF0LD_1RE1LC_1RA1RE_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RD0LE_0LC1RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB0RA_1LC---_1LF0LD_1RE0RC_0RE1RA_0LF0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1LB0LE_1RC1LB_0LA0RD_1RB1RD_0LF1LA_---0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB1LA_1RC0RE_1RD---_0LA0LD_1LF1RE_1LD0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RD0LE_0RC1RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB0RE_1LC---_0LC1LD_1RA0LC_0RE1RF_1RB0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0LF0LA_---1RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB1LA_1RC0RE_1LD---_1LF0RB_1LD1RE_0LA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB1LA_1RC0RD_0LD---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_0LE0RB_---0LA_1LE1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_0RE0LC_1RF0LE_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1LB---_1RC1LB_1RA0RD_1LE1RD_1LF0RC_0LB0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1LB---_0LC0LF_1RD1RA_0RD1RE_0RA0RE_0LF0LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB1LA_0LC0RE_0LF0LD_1RE1LC_1RA1RE_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 2 3200 0 8 0 0). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1LB1LA_1RC1RF_0RE0RD_0LB0RC_0LA0RF_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1LB0RC_1RA0RA_1LC0LD_1LE0LE_1RF1LE_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB1LA_0RC0RD_0RD---_1LE1RD_1LF0RB_0LA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1LB0RC_0LC0LE_1RD1RC_1RA1LD_0LF1RE_---1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_0LB0LA_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_1LF1LD_---1RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LE_0RC0RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RE1LF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RF_0RE1LD_1LC1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1LB0RF_1RC1LB_1RA0RD_1LE1RD_0LC0LB_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA1RF_1LA1LD_0RC0RB_---1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB0LC_1LC0RD_1RF1LA_0RD1RE_0RF0RE_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB1LA_1RC0RD_1RD1RF_1LE1RD_0LB0LA_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1RF_0RE1RA_0LF0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB0LE_0LC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1LB0RD_1RC0LE_1RA1LC_1RC1RD_1LF1LB_---0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_1LF1LD_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RB0LE_1LF1LD_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB0LC_1LC0RD_0LC1LA_0RD1RE_0RF0RE_0LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0RF---_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LE_0LC0RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB0RE_0LC1LD_---1LD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB1LA_0LC0RF_1LD1RC_---0LE_1RF0LC_1RA1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA0RF_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB0LE_1RC1RB_1RD1LC_0LE0RB_1LF1RE_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RA_1RB0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA0RF_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_1RA0LE_0LF1LD_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB1LA_0LC0RE_0RF0LD_1RE1LC_1RA1RE_---1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0RF0LA_---1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1LA0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1RB0RA_0LB1RC_1LD---_0LD0LE_1RF0RC_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1RB0RA_0LC---_1LD1RC_0LD0LE_1RF0RC_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1RB1RE_0LC0RD_1LA1LC_0RE0RB_0LA1RF_---0LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1LB---_1RC1LE_0RC0RD_1RA1RF_0LE0LB_0RA0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1RB1LF_1RC1RB_1RD1LC_0LE0RB_---0LA_0LE0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1RB0LE_1LC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1RB0LD_1RC0RE_0LA0RF_1LA1LD_0RC0RB_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1RB0RA_1LC---_1RE1LD_1RE0LC_0LD0RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1RB0RA_1LC0LE_0LC1LD_0RB0LC_1RF---_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1RE0LF_1RA1RE_1LC1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE0RB_0LE1RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1RB0RA_1LC---_0RE1LD_1RE0LC_0LD0RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1RB0RF_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1RF_0RE1RA_1LF0LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1RB0LF_1RC1RB_1RD1LC_1LE0RB_---0LA_1LE1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1RB1LA_0LC0RE_---0LD_1RE1LF_1RA1RE_0LC0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1RB---_1LC---_0LC0LD_1RE0RB_0RE1RF_1RB0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1RB0RA_1LC---_0LF0LD_1RE0RB_0RE1RA_0LF0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1RB1LE_1RC1RB_1RD1LC_0LE0RB_0LF0LA_---0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LC_---0RF_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1RB1RA_1RC1LB_0LD0RA_0LA0LE_0LF1LD_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 1 0). Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB1RE_0RD0LF_1LD---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB0RA_0RD0LF_1LD---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt98: ~halts (TM_from_str "1RB1LF_0RC0RB_1LC1RD_1RB1LE_---0LA_1RC0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt99: ~halts (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA0LE_1LF1RE_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt100: ~halts (TM_from_str "1LB1LD_1RC1RB_0LA0RC_---0LE_1LF1LE_1LC0RB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt101: ~halts (TM_from_str "1RB0LF_0LC0RE_0RE0LD_1LE---_0RA1RC_1LA1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt102: ~halts (TM_from_str "1RB0LF_0LC0RE_0RE0LD_1LE---_0RA0RF_1LA1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt103: ~halts (TM_from_str "1RB0LD_0RC0RE_1LD---_0LD1LA_0RE1RF_1RC0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt104: ~halts (TM_from_str "1RB0RE_1LC1LD_---1RD_0LE0LB_1RF1RE_1RA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 4 0). Time Qed.

Lemma nonhalt105: ~halts (TM_from_str "1RB0RA_1LC---_0LC1LD_1RE0LC_0RE0RF_1LE1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt106: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB1RE_0RD0LF_0LA---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 0 14 2 0). Time Qed.

Lemma nonhalt107: ~halts (TM_from_str "1RB0RE_0RC0RE_1LD---_0LD1LA_1RF0RC_0LA0RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt108: ~halts (TM_from_str "1RB0LE_0LC0RF_0RF0LD_0LE---_1LA1LB_0RA0RE") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt109: ~halts (TM_from_str "1LB0LB_1RC1LB_---0RD_1RE0RE_1LD0RF_1LF0LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt110: ~halts (TM_from_str "1RB1LD_0RC0RB_1LC1RA_---0LE_1RB1LF_1RC0LA") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 0 14 2 0). Time Qed.

Lemma nonhalt111: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_0LE0LF_1RA1RE_0LC1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt112: ~halts (TM_from_str "1LB0RC_1RC0LE_1RD1RC_1RA1LD_1LF1RE_---0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt113: ~halts (TM_from_str "1RB1LA_1LC0RE_1LF1LD_1RA0LC_1RA1RE_---0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt114: ~halts (TM_from_str "1RB0RF_0RC1RE_1LD---_0LD1LA_0LA0RE_1RE0RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt115: ~halts (TM_from_str "1RB0RA_1LC1RA_0RE1LD_1RE0LF_0LF0RB_0LC---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt116: ~halts (TM_from_str "1LB0RC_0LC0LE_1RD1RC_1RA1LD_1LF1LB_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt117: ~halts (TM_from_str "1RB0RA_1LC---_0LC0LD_1RE1LF_0RE1RA_0RF0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt118: ~halts (TM_from_str "1RB1LA_1LC0RE_1LF1LD_0LE0LC_1RA1RE_---1RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt119: ~halts (TM_from_str "1RB1RA_1LC0RE_1RA0LD_1LC1RD_1RA0RF_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt120: ~halts (TM_from_str "1RB0LE_1RC0RF_1RD0RC_1LE---_0LE1LA_0RF1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt121: ~halts (TM_from_str "1RB0RA_1LC---_0RE1LD_1RE0LC_0LD0RF_1LC1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt122: ~halts (TM_from_str "1RB1LA_1LC0RE_0LF1LD_0LE0LC_1RA1RE_---1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt123: ~halts (TM_from_str "1RB1LA_1LC0RE_---1LD_0LE0LF_1RA1RE_0LC1LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 3 0). Time Qed.

Lemma nonhalt124: ~halts (TM_from_str "1RB1LA_1RC0RD_1LA0RF_1LE1RD_0LB0LA_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt125: ~halts (TM_from_str "1LB0LB_1RC1LF_1LA0RD_1RE0RE_0LA0RE_1LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt126: ~halts (TM_from_str "1RB0RF_1LC0RE_0LC0LD_1LA---_0RE1RF_0RA1LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt127: ~halts (TM_from_str "1LB1RA_0LC0LE_1RD0RA_1LA1RF_1RC1LE_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt128: ~halts (TM_from_str "1RB0RD_1LC0RC_0RC1RD_0RA1LE_0LE0LF_1LA---") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt129: ~halts (TM_from_str "1LB0RF_1RB0RC_1LD1RA_0LD1LE_0LF---_0RA0LD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt130: ~halts (TM_from_str "1RB1LA_1RC0RD_1LD0LB_0LA1RE_1RF0RC_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt131: ~halts (TM_from_str "1LB1RA_0LC0LE_1RD0RA_1LE0RF_1RC1LE_---1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt132: ~halts (TM_from_str "1RB0RC_1LC0LA_0LE1RD_1RF0RB_1RA1LE_---1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt133: ~halts (TM_from_str "1RB1LE_1RC0RB_0RD1RC_0LE---_1LF0LF_1LA1RF") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 6 3200 0 7 1 0). Time Qed.

Lemma nonhalt134: ~halts (TM_from_str "1LB1RA_0LC0LE_1RD0RA_1RA1RF_1RC1LE_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt135: ~halts (TM_from_str "1LB1RA_0LC0LE_1RD0RA_1LE0RF_1RC1LE_---0RE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt136: ~halts (TM_from_str "1LB0RF_1RC1LB_1RA0RD_1LE1RD_0LC0LB_---1RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt137: ~halts (TM_from_str "1LB0LB_1RC1LC_1LA0RD_1RE0RF_0LA0RE_---0RE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt138: ~halts (TM_from_str "1RB0RC_1LC1RF_1LD1RC_0LA0LE_1RA1LE_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt139: ~halts (TM_from_str "1LB0LB_1RC1LC_1LA0RD_1RE1RF_0LA0RE_---1LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt140: ~halts (TM_from_str "1LB0RF_1RB0RC_1LD1RA_0LD1LE_0LF---_0RA0RD") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt141: ~halts (TM_from_str "1RB1LA_1RC0RD_1LD1RF_1LE1RD_0LB0LA_---0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt142: ~halts (TM_from_str "1RB0RC_1RC1RF_1LD1RC_0LA0LE_1RA1LE_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt143: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB0RA_0RD0LF_0LA---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt144: ~halts (TM_from_str "1LB1LC_1RC0LA_0LE0RD_0RB0RA_1RB0LF_1LD---") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt145: ~halts (TM_from_str "1RB1LF_1RC0RB_1RD1RC_0LE---_1LA1RE_1LE0LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 3 0). Time Qed.

Lemma nonhalt146: ~halts (TM_from_str "1RB0LE_0LC0RF_0RF0LD_0LE---_1LA1LB_0RA1RC") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt147: ~halts (TM_from_str "1RB1RE_0LC1LB_1RD1LB_1RA1RD_0RD0RF_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt148: ~halts (TM_from_str "1LB0RD_0LC0RB_1LD1LE_1RB1RD_---0LF_1LA1LF") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt149: ~halts (TM_from_str "1RB0LF_0LC0RE_1RA0LD_1LE---_0RA0RF_1LA1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 2000 1000 4 3200 1 15 0 0). Time Qed.

Lemma nonhalt150: ~halts (TM_from_str "1RB1LE_1RC0RB_1RD1RC_1LA---_1LF0LF_1LA1RF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt151: ~halts (TM_from_str "1RB1RA_0LC0RE_1LD1RC_1RA0LC_1RA0RF_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 6 0). Time Qed.

Lemma nonhalt152: ~halts (TM_from_str "1RB1RA_1LC0RE_1RA0LD_1LC1RB_1RA0RF_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 6 0). Time Qed.

Lemma nonhalt153: ~halts (TM_from_str "1LB0RD_0LC0LB_1RD1LC_1LD0RE_1LF1RE_---1LA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt154: ~halts (TM_from_str "1RB0RA_0RC---_1LD---_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt155: ~halts (TM_from_str "1RB0RA_0RC---_1LD1RA_0LD0LE_1RF0RB_0RF1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt156: ~halts (TM_from_str "1RB0RA_0RC1RA_1LD---_0LD0LE_1RF0RB_0RF1LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt157: ~halts (TM_from_str "1RB0RA_1RC0LD_1LB---_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt158: ~halts (TM_from_str "1RB1LA_1LB0RC_1LD1RC_---1LE_1LF0RB_0LA0LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt159: ~halts (TM_from_str "1RB0RA_1RC1LE_1LD---_1RF0RB_0LE0LD_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt160: ~halts (TM_from_str "1LB---_1RC0RE_0RC1RD_1RE0RD_1RA1LF_0LF0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt161: ~halts (TM_from_str "1RB0RA_1RC---_1LC0LD_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt162: ~halts (TM_from_str "1RB0RA_0RC---_1LB1LD_0LD0LE_1RF0RB_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 6 1 0). Time Qed.

Lemma nonhalt163: ~halts (TM_from_str "1LB0RA_1RC1LF_0RC0RD_0RE1LE_1RA---_0LF0LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 3 0). Time Qed.

Lemma nonhalt164: ~halts (TM_from_str "1RB1RE_0LC1RA_0RD1LC_1LA1LB_0RA0RF_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt165: ~halts (TM_from_str "1RB0RC_1RC0RA_1LD1RB_1RD1RE_---0LF_0LA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt166: ~halts (TM_from_str "1LB1RE_0LC1LB_1RD1LB_1RA1RD_0RD0RF_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 6 12 0). Time Qed.

Lemma nonhalt167: ~halts (TM_from_str "1RB0LE_1LC1RF_1RE0LD_0LE1LD_1RC0RA_---0LE") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt168: ~halts (TM_from_str "1RB0LE_1LC0RF_1RE0LD_0LE1LD_1RC0RA_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt169: ~halts (TM_from_str "1LB1RD_1LC1LA_1RA0LB_---0RE_1RF1RE_0LC1LB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 3 12 0). Time Qed.

Lemma nonhalt170: ~halts (TM_from_str "1LB0LD_1LC0RD_0LD1LF_1RE0RA_0RF---_0LB0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt171: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1LD0LE_0LF1LD_1RF0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt172: ~halts (TM_from_str "1RB0RA_0RC---_1LD0RB_0LD0LE_1RF1LB_0RF1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt173: ~halts (TM_from_str "1LB0RA_1RB0RC_0RD1RA_1LE---_0LE1LF_1RC0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt174: ~halts (TM_from_str "1RB0RA_0RC0RA_0LC1LD_1LE---_0LF0LA_1RA0LC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt175: ~halts (TM_from_str "1RB0RA_0RC0RA_0LC1LD_1LE---_0LF0LA_1RA0RC") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt176: ~halts (TM_from_str "1RB0RF_0RC1RE_1LD---_0LD1LA_1LF0RE_1RF0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt177: ~halts (TM_from_str "1RB1LD_1RC---_0LA0RC_1LD0LE_0LF1RC_1RF0RB") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt178: ~halts (TM_from_str "1LB0RA_1RC0RF_1RA0RD_1LE---_0LE0LB_0RD1RA") c0.
Proof. solve_cert (RWL_mod_FAR 2000 1000 1 3200 2 2 2 0). Time Qed.

Lemma nonhalt179: ~halts (TM_from_str "1RB0LE_0RC1RA_1LD0RA_1LA---_0RC0LF_0LD1LE") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 2 3200 0 2 2 0). Time Qed.

Lemma nonhalt180: ~halts (TM_from_str "1RB0LE_0RC1LF_1RD1RB_0LA0RB_1LB---_0LB0LD") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt181: ~halts (TM_from_str "1LB---_0RC1LF_1RD1RB_0LE0RB_1RB0LA_0LB0LD") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt182: ~halts (TM_from_str "1RB1RE_0LC0RE_1RE0LD_1LE---_0RA1LF_0LE0LB") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt183: ~halts (TM_from_str "1RB1LC_0LC0RD_1LA0LC_1RB0RE_---1RF_1LC0LB") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 3 0). Time Qed.

Lemma nonhalt184: ~halts (TM_from_str "1RB0RE_0LC0RA_1LD0LC_1RB1LC_---1RF_1LC0LB") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 3 0). Time Qed.

Lemma nonhalt185: ~halts (TM_from_str "1LB0LA_1RC1LA_0LA0RD_1RC0RE_---1RF_1LA0LC") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 3 0). Time Qed.

Lemma nonhalt186: ~halts (TM_from_str "1RB0LF_1RC---_0RD0RF_1LE1RC_1LA0RA_0LE0LA") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 3 0). Time Qed.

Lemma nonhalt187: ~halts (TM_from_str "1RB1LB_0LC0RE_0RA1LD_1LC0RF_0LB0RD_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt188: ~halts (TM_from_str "1RB1LE_1RC0RF_0RD0RD_0LE0RB_0LA1LE_---0RE") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt189: ~halts (TM_from_str "1RB0RF_0RC0RC_0LD0RA_0LE1LD_1RA1RC_---0RD") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt190: ~halts (TM_from_str "1RB0LD_0LC0RD_1RA1LC_0LB0RE_1LB0RF_---1RA") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt191: ~halts (TM_from_str "1RB1RD_1RC0RF_0RD0RD_0LE0RB_0LA1LE_---0RE") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt192: ~halts (TM_from_str "1RB0RF_0RC0RC_0LD0RA_0LE1LD_1RA1LD_---0RD") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt193: ~halts (TM_from_str "1LB0RF_0LC0RE_1RD1LC_1RB0LE_0LB0RA_---1RD") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt194: ~halts (TM_from_str "1LB0RF_0RC1LA_1RD1LD_0LB0RE_0LD0RA_---0RC") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt195: ~halts (TM_from_str "1RB1LA_1RC0LD_0LA0RD_0LC0RE_1LC0RF_---1RB") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 4 2 0). Time Qed.

Lemma nonhalt196: ~halts (TM_from_str "1LB0LB_1RC1LF_1LA0RD_1RE1RC_0LA0RE_1LA---") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 3 3200 1 3 0 0). Time Qed.

Lemma nonhalt197: ~halts (TM_from_str "1LB0LB_1RC1LC_1LA0RD_1RE0RF_0LA0RE_---1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 3 3200 1 3 0 0). Time Qed.

Lemma nonhalt198: ~halts (TM_from_str "1LB0LB_1RC1LC_1LA0RD_1RE1RF_0LA0RE_---0RD") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 3 3200 1 3 0 0). Time Qed.

Lemma nonhalt199: ~halts (TM_from_str "1LB0LB_1RC1LC_1LA1LD_1RF1RE_---0RD_0LA0RF") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 3 3200 1 3 0 0). Time Qed.

Lemma nonhalt200: ~halts (TM_from_str "1LB1RC_0RA1LD_1RA0RA_0LF1LE_0LB1LE_---1LC") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 12 3200 2 1 8 0). Time Qed.

Lemma nonhalt201: ~halts (TM_from_str "1LB1RC_0RA1LD_1RA0RA_0LF1RE_0LB1LE_---1LC") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 12 3200 2 1 8 0). Time Qed.

Lemma nonhalt202: ~halts (TM_from_str "1LB1RC_0RA1LD_1RA0RA_0LF1LE_0LB1RB_---1LC") c0.
Proof. solve_cert (CPS_LRU_FAR 6000 3000 12 3200 0 11 1 0). Time Qed.

Lemma nonhalt203: ~halts (TM_from_str "1LB1RC_0RA1LD_1RA0LE_0LF1LE_0LB1RB_---1LC") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 4 3200 2 3 4 0). Time Qed.

Lemma nonhalt204: ~halts (TM_from_str "1LB0RA_1RC1LE_0RC0RD_1RA1LD_0LF---_0LF0LB") c0.
Proof. solve_cert (RWL_mod_FAR 6000 3000 1 3200 2 6 2 0). Time Qed.

Lemma nonhalt205: ~halts (TM_from_str "1LB0RC_1LC1LD_0RD1RC_1LE0RC_0LF---_0LA1LF") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 2 3200 2 2 12 0). Time Qed.

Lemma nonhalt206: ~halts (TM_from_str "1RB1LD_1LB0RC_1LA1RC_1LE0LF_0LA0LE_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 2 3200 2 3 3 0). Time Qed.

Lemma nonhalt207: ~halts (TM_from_str "1RB1RC_1LC---_0RF0LD_1LE0LC_1RF1RE_0RA1LD") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0). Time Qed.

Lemma nonhalt208: ~halts (TM_from_str "1LB0LD_1RC1RB_0RE1LA_0RC0LA_1RF1RD_1LD---") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0). Time Qed.

Lemma nonhalt209: ~halts (TM_from_str "1LB---_0RC0LD_0RF1LD_1LE0LB_1RC1RE_1RA1RB") c0.
Proof. solve_cert (RWL_mod_FAR 20000 10000 3 3200 2 4 2 0). Time Qed.

Lemma nonhalt210: ~halts (TM_from_str "1RB1RD_1RC0LA_1LD0RA_0LE1LB_---1LF_1RF0LD") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 3 3200 1 2 0 0). Time Qed.

Lemma nonhalt211: ~halts (TM_from_str "1RB0LD_1RC1RA_1RD0RA_0RE0RD_1LF---_0LF1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt212: ~halts (TM_from_str "1LB---_1RC0RD_1LB0RB_1RB0LE_1LD1LF_0LD1LA") c0.
Proof. solve_cert (CPS_LRU_FAR 20000 10000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt213: ~halts (TM_from_str "1LB0RB_1LC1RC_1RD1LE_0LF0RA_1LD0LA_---0RA") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt214: ~halts (TM_from_str "1RB1LF_0LC0RD_---0RD_1LE0RE_1LA1RA_1LB0LD") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt215: ~halts (TM_from_str "1LB0RB_1LC1RC_1RD1LE_1LF0RA_1LD0LA_---1LC") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt216: ~halts (TM_from_str "1RB1LF_1LC0RD_---1LA_1LE0RE_1LA1RA_1LB0LD") c0.
Proof. solve_cert (RWL_mod_FAR 60000 30000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt217: ~halts (TM_from_str "1LB1RD_0RC0LE_1RD1RC_1LB0RC_1LF1LA_---1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 24 1). Time Qed.

Lemma nonhalt218: ~halts (TM_from_str "1LB1LA_1RC1RD_0LA0RD_0LB0RE_1RF1LC_---0RA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 2 12 2). Time Qed.

Lemma nonhalt219: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_1RF1RE_1RB1LA_---1LB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 12 2). Time Qed.

Lemma nonhalt220: ~halts (TM_from_str "1LB1RC_1RC0LD_1RA0RC_1LE1LF_1RA1LB_---0RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 3 24 1). Time Qed.

Lemma nonhalt221: ~halts (TM_from_str "1LB0RE_1LC1RB_0RD1LD_0LF1RA_1LD1RE_---0LB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt222: ~halts (TM_from_str "1LB0LC_0LC0RD_1RA1LE_0RA1RD_0LF0LD_---1RC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt223: ~halts (TM_from_str "1RB1LA_0RC1LD_1LD0RE_1RD0LA_1RF1LE_---1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt224: ~halts (TM_from_str "1LB0LF_0RC1LE_1LD1RB_1LD0LA_---1RC_1LA1RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt225: ~halts (TM_from_str "1LB1RD_0LC0RA_1RA0LE_0RA1RD_1LF1RE_---0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt226: ~halts (TM_from_str "1LB1RD_0RC0LE_1RD1RC_1LB0RC_0LF1RE_---1LA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt227: ~halts (TM_from_str "1RB0RE_0LC0RD_1LA1LC_1RE0RE_0LF1LB_1RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt228: ~halts (TM_from_str "1LB1RD_0RC0LE_1RD1RC_1LB0RC_0LF1LA_---1LA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt229: ~halts (TM_from_str "1RB1LA_0RC1LE_1LD0RF_1RE1RB_---0LA_1RD1LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt230: ~halts (TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1LB---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt231: ~halts (TM_from_str "1LB0RE_1LC1RB_0RD0LE_0LF1RA_1LD1RE_---0LB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt232: ~halts (TM_from_str "1LB1RD_0RC0LE_1RD1RC_1LB0LF_1LF1LA_---1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt233: ~halts (TM_from_str "1RB0LA_0RC1LE_1RD0RD_0LE1RF_---1LA_1RC1RA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 3 12 1). Time Qed.

Lemma nonhalt234: ~halts (TM_from_str "1LB0RF_1RC0LB_0RE0RD_1RA0RA_0LA1RD_1LC---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt235: ~halts (TM_from_str "1RB0RC_0RC0LD_1LA0RE_0LA1LD_1RF1LE_---0RD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt236: ~halts (TM_from_str "1LB1RA_0LC1RD_0RD0LE_1RA0RA_1LF1RE_---1LB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt237: ~halts (TM_from_str "1LB0LF_0RC1LE_1LD1RB_0LE0LA_---1RC_1LA1RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt238: ~halts (TM_from_str "1LB0RC_0RC0LD_1RA1RC_0LE1RD_---1LF_1LB1RA") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt239: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_1RE0RE_0LF1LB_1RA---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt240: ~halts (TM_from_str "1LB1RC_1RC0LD_1RA0RC_1LE0LF_1RA1LB_---1LE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt241: ~halts (TM_from_str "1RB0LA_0RC0RE_0LD1RE_1LA0RF_1RD0RD_1RE---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt242: ~halts (TM_from_str "1LB1RD_0LC0RD_1RA0LE_0RA1RD_1LF1RE_---0LD") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt243: ~halts (TM_from_str "1RB---_1RC0RC_1LD0RA_1RE0LD_0RF0RB_0LC1RB") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt244: ~halts (TM_from_str "1RB1LF_1RC1RA_1RD0LA_0LE0RC_---1LA_0LD1LC") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt245: ~halts (TM_from_str "1LB0RF_1RC0LB_0RE0RD_1RA0RA_0LA1RD_1RD---") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt246: ~halts (TM_from_str "1LB---_0RC0RD_0LE1RD_1RE0RE_1LF0RA_1RB0LF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt247: ~halts (TM_from_str "1RB0LC_0LC0RD_1LA1LC_0RF1RE_1RB1LA_---1RE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 2 24 1). Time Qed.

Lemma nonhalt248: ~halts (TM_from_str "1LB0LD_1RC0LA_1RA0RB_1LA0RE_1RF---_0RC0RE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 4 5 24 0). Time Qed.

Lemma nonhalt249: ~halts (TM_from_str "1RB0LC_1RC0RA_1LA0LD_1LC0RE_1RF---_0RB0RE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 5 24 2). Time Qed.

Lemma nonhalt250: ~halts (TM_from_str "1LB0LD_0LC0LF_0RD1LF_0LE1RC_1LC---_1LA0RF") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 2 0 0 1 2 1 24 0). Time Qed.

Lemma nonhalt251: ~halts (TM_from_str "1LB0RE_1LC0LA_1RD0LB_1RB0RC_1RF---_0RD0RE") c0.
Proof. solve_cert (RNGS_mod_QSym_FAR 200000 100000 0 0 0 1 2 6 24 0). Time Qed.

