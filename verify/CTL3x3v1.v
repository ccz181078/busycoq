From BusyCoq Require Import CTL33.

Lemma nonhalt1: ~halts (TM_from_str "1RB2RB2LA_2LC1RB0RB_0LB1LA---") c0.
Proof. solve_cert (NG 0 300 300 1 6 8 0 true). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB2LA0LA_2RC---0RB_1LA2LA2RC") c0.
Proof. solve_cert (NG 0 300 300 1 8 2 0 true). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB2LA0RB_2LC1RB2RB_---1LA0LC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB0LA2RA_1LC---0RC_1RA2LC0LC") c0.
Proof. solve_cert (NG 0 300 300 2 2 0 0 true). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB---0LB_1LC2RB0RB_1LA1LA2LC") c0.
Proof. solve_cert (NG 0 300 300 2 0 2 0 true). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB2LC0LA_0LB1RC---_1LA2RC0RC") c0.
Proof. solve_cert (RWL_mod 1001 300 300 1 3200 2 1 1 0). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB0RA---_2LC0LC2RB_2RA0LC1LC") c0.
Proof. solve_cert (NG 0 300 300 1 1 6 0 true). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB1LA0LA_2RC0RB---_2LA0LA1RC") c0.
Proof. solve_cert (NG 0 300 300 1 1 6 0 true). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB1LA0LA_2RC0RB---_2LA2RC1RC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB2LA0LA_2RC---0RB_1LA1RC2RC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB---0RA_1LC2RB1RB_2RA0LC2LC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB0RA---_2LC1RB1LC_2RA0LC1LC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB---0RA_1LC2RB0LC_2RA0LC2LC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB0RA---_2LC1RB2RB_2RA0LC1LC") c0.
Proof. solve_cert (NG 0 300 300 1 6 8 0 true). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB2RB2LA_2LC1RB0RB_0LC1LA---") c0.
Proof. solve_cert (NG 0 300 300 1 6 8 0 true). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB2RB1LA_1LC0RB1RB_0LC2LA---") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB1LA0RB_1LC2RB1RB_---2LA0LC") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB2LA0LA_2RC---0RB_1LA1RC0LA") c0.
Proof. solve_cert (NG 0 300 300 1 8 6 0 true). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB2LA1LA_1LA2RC2LB_---2RB0RC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB2LA1LA_2LA0RC2RB_---2RC1RA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB2LA0LA_1LA2RA0RC_---0LA0RB") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB2LA0LA_1RC1LC2RB_1LA---0RA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB---0LB_1LC2RB0RB_1LA0RC2LC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB2LA0LA_1RC0LB2RB_1LA---0RA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB0LB1RA_2LC1RB2RB_---2LA1LC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB2LA0LA_1LC2RA0RB_0RC1LA---") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB---1LC_1LC2LA0RB_2RB2LC1RA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB1RB2RA_1LC---0RC_1RA2LC0LC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB2LA0LA_1RC1RC2RB_1LA---0RA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB1LB2RA_1LC---0RC_1RA2LC0LC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB2LA1RC_1LB1LA2RB_---0RA0LA") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB1LA0LC_2LA2RB1RB_---2LB1LC") c0.
Proof. solve_cert (NG 0 300 300 1 4 0 0 true). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB1LC0LA_2RC0RB---_1LA2LA2RC") c0.
Proof. solve_cert (NG 0 300 300 2 0 2 0 true). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB---0RA_2LC1RB1LC_2RA0LC2LB") c0.
Proof. solve_cert (NG 0 300 300 2 0 2 0 true). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB---1LB_2LC2RB0LC_0LA1RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 300 300 3 3200 2 1 1 0). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB0RB1LA_0RC0LC2LC_2LA2RA---") c0.
Proof. solve_cert (RWL_mod 1001 300 300 3 3200 2 1 1 0). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB2LA1LA_2LC0RC0LC_---2RA2LA") c0.
Proof. solve_cert (NG 0 300 300 1 1 4 0 true). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB0LB0RA_2LA0LC1RA_2RA2LB---") c0.
Proof. solve_cert (NG 0 300 300 1 1 2 0 true). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB1LA2LA_1LA2RC1LB_---2RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB---1LC_2RC0RB0LC_1LB2RB0LA") c0.
Proof. solve_cert (NG 0 1000 1000 2 1 2 0 true). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB2LA1RA_1LB1LA2RC_---1LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 8 0 0). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB2LA1RA_1LB1LA2RC_---0LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 2 0 0). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB---0RB_1LC2RA1RB_2RA2LC0LC") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB2LB1RA_2RC2LA0LA_1LB---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 2 10 0 0). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB1LA0LA_0RC1RB2RB_1LC2LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB2LA1RA_1LC1RA2RC_---1LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 8 0 0). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB0RB2LA_2RC0LB1LB_2LB1RA---") c0.
Proof. solve_cert (NG 0 1000 1000 1 4 2 0 true). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB2LA0LA_1LA---2RC_2RA1LC0RA") c0.
Proof. solve_cert (NG 0 1000 1000 2 1 2 0 true). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB2LA1RA_1LC2RC2RC_---1LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 2 3200 2 2 6 0). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB0LA1LA_2RC0RC---_2LA2RC1RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB0LA2LA_2RC---0RC_1LA1RA2RC") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB0LA2LA_2RC---0RC_1LA1RB2RC") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB---2LC_2LC2RB2RC_1LA2LC0RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 8 0 0). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB0RB---_2LC1RB2RA_2RA1LC0LC") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB2LA1RA_1LC1LA2RC_---1LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 8 0 0). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB1LA0LA_2LA1RB0RC_1LC2RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB0LC2LA_2LA0RB2RB_2RC---1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB2LB2LA_1LA2RC1LB_---2RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 2 12 0). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB2LA1RA_1LB1LA2RC_---1RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB2LA1RA_1LC1RB2RC_---1LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 4 0). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB0LA1RC_2LC2LB---_1RA1LA0RC") c0.
Proof. solve_cert (NG 0 1000 1000 2 4 0 0 false). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB1LB0RA_1RC0LB1RA_2LA2LC---") c0.
Proof. solve_cert (NG 0 1000 1000 2 4 0 0 false). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB---1RA_2LC0LB2RC_2LA2LB0RC") c0.
Proof. solve_cert (NG 0 1000 1000 2 4 0 0 false). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB0RC---_0LC0RB0LA_2RA1LC1LB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 3 3200 1 14 1 0). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB0RB0LA_1LB2RA2LC_2RC---2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB0LB---_2LC0RB2RB_1LA0RC1RC") c0.
Proof. solve_cert (NG 0 3000 3000 4 6 8 0 true). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB0RB1LA_2RC2LB0LB_1LA---1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 4 2 0). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB0LB0RC_0LB2LC---_1RA2RC1LC") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 2 9 1 0). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB0RB---_1LC0RA1LB_2RB0LB0LA") c0.
Proof. solve_cert (NG 0 3000 3000 5 8 8 0 true). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB1LB1LA_2RC0LA1RB_2LA1RB---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 12 0 0). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB---1LB_1LC0LC1RB_2LA2RC0RC") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 4 2 0). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB0LB1RA_1LA2LC1LA_---2RA2LA") c0.
Proof. solve_cert (NG 0 3000 3000 1 8 2 0 true). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB2RC1RB_1LA0RA1LB_---2LB2RB") c0.
Proof. solve_cert (NG 0 3000 3000 1 8 2 0 true). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1RB0LC1RA_2LA0RA0RC_1LA0LA---") c0.
Proof. solve_cert (NG 0 3000 3000 5 8 8 0 true). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1RB1LA---_2RC0LB0RC_2LC2LA1RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 3 3200 1 2 1 0). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1RB2LA2LC_0LA0LA1RA_---2RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 3 6 0). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1RB0LA2LA_2RC---0RC_1LA2LB2RC") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 3 3200 0 2 0 0). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1RB0RB---_2LC1RB1LA_2RA1LC0LC") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 3 3 0). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1RB0LB0RC_1LB2LC---_1RA2RC1LC") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 3 3200 2 5 1 0). Time Qed.

