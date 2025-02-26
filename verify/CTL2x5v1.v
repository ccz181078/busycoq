From BusyCoq Require Import CTL25.

Lemma nonhalt1: ~halts (TM_from_str "1RB3LB4RA---2LB_2LA0RA4RB0RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 5 1 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB3RB---4LA0RA_2LA3RA1LA1LB1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 3 8 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1RB4RA---1LB1LA_2LB3RB3LB4LA4RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 3 16 0). Time Qed.

Lemma nonhalt4: ~halts (TM_from_str "1RB2LA4LA---2RB_2LA3LA1LB4RB1RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 18 3200 1 2 0 0). Time Qed.

Lemma nonhalt5: ~halts (TM_from_str "1RB2RB3RB4LA2LA_0LA---0LB1RA3RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 5 1 0). Time Qed.

Lemma nonhalt6: ~halts (TM_from_str "1RB3RB---1RA0LB_2LA4LA4RB2LB3RA") c0.
Proof. solve_cert (NG 0 1000 1000 3 8 2 0 true). Time Qed.

Lemma nonhalt7: ~halts (TM_from_str "1RB2RA3LB4RB0LA_2LA---3LA0RA2LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 3 3200 2 2 4 0). Time Qed.

Lemma nonhalt8: ~halts (TM_from_str "1RB2RA1LA4RB2LB_2LA3RB1RA0LB---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt9: ~halts (TM_from_str "1RB3LB0RB0RA---_2LA4RA0RA0LB3RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 20 3200 0 2 0 0). Time Qed.

Lemma nonhalt10: ~halts (TM_from_str "1RB2RB3RB4LA2LA_0LA---3LB1RB3RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt11: ~halts (TM_from_str "1RB2LB1RB4LA---_2LA4LA3LB1RA2RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt12: ~halts (TM_from_str "1RB3RA4RB2LB1LA_2LA2LA1RA4RB---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt13: ~halts (TM_from_str "1RB3LA---1RA3RB_2LA4RB1RA1LB1LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 1 13 2 0). Time Qed.

Lemma nonhalt14: ~halts (TM_from_str "1RB1LA4RA1RA0RB_2LA2LB3RB2LA---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 1 2 0 0). Time Qed.

Lemma nonhalt15: ~halts (TM_from_str "1RB2LB3LA0RA---_2LA2RB1LB4LA1RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 0 16 0 0). Time Qed.

Lemma nonhalt16: ~halts (TM_from_str "1RB1RA3RB0RB0LB_2LA4RB1LA---2RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 5 3200 1 5 0 0). Time Qed.

Lemma nonhalt17: ~halts (TM_from_str "1RB3LA0LB0LA1RA_2LA1RA4LA4RB---") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt18: ~halts (TM_from_str "1RB3LA1LB0LA1RA_2LA1RB4LA4RB---") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt19: ~halts (TM_from_str "1RB2RA1LA4LB1RA_2LA3RB4RA2LB---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 5 3200 2 13 1 0). Time Qed.

Lemma nonhalt20: ~halts (TM_from_str "1RB4LA1RA---0LA_2LB3LA1RB1RA2RB") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt21: ~halts (TM_from_str "1RB2LA0LB2LB---_2LA3RA0LB4LB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 0 16 0 0). Time Qed.

Lemma nonhalt22: ~halts (TM_from_str "1RB2LB4LB---1LB_2LA0LA3RA0RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 18 3200 2 6 1 0). Time Qed.

Lemma nonhalt23: ~halts (TM_from_str "1RB3LA1LB---0RB_2LA2RB1LA4RA2LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt24: ~halts (TM_from_str "1RB2LA1RA4LA0RB_1LA3LA2RB---2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt25: ~halts (TM_from_str "1RB3LA0LA1RA---_2LA4RB4LB4LB3RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt26: ~halts (TM_from_str "1RB2LA1RA4LA0LB_1LA3LA2RB---2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt27: ~halts (TM_from_str "1RB2LA1RA4LA0RB_1LA3LA2RB---2LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt28: ~halts (TM_from_str "1RB2RA3RB1LA---_2LA3RB4LA0LA3LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt29: ~halts (TM_from_str "1RB2RB3LA2RA---_2LA4RB3RB2LB2RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 8 0). Time Qed.

Lemma nonhalt30: ~halts (TM_from_str "1RB2LA1RA4RA0RB_1LA3RB3LB2RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt31: ~halts (TM_from_str "1RB3LA4LA1RA0RB_2LA3RB1LA1LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt32: ~halts (TM_from_str "1RB3RA1LA1LB0LA_2LA2RB1RA4RB---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 16 3200 0 8 0 0). Time Qed.

Lemma nonhalt33: ~halts (TM_from_str "1RB2LA4LA4LB2RA_1LA4RB3RB---1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt34: ~halts (TM_from_str "1RB3LA4LA1RA1LA_2LA3RB3RB1LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt35: ~halts (TM_from_str "1RB3LA1LA4LB---_2LA1RB3RB1RA0RB") c0.
Proof. solve_cert (NG 0 1000 1000 3 1 8 0 true). Time Qed.

Lemma nonhalt36: ~halts (TM_from_str "1RB3LA3RA2LA---_2LA3LA4LB4RB2RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt37: ~halts (TM_from_str "1RB2RA3RB0LA---_2LA2RB1LB4LA2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 1 2 0). Time Qed.

Lemma nonhalt38: ~halts (TM_from_str "1RB3LB1LA4LA0RA_2LA3RA0RA---2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 1 2 0). Time Qed.

Lemma nonhalt39: ~halts (TM_from_str "1RB3LA1LA1RA3LB_2LB3RA---4RB1LA") c0.
Proof. solve_cert (NG 0 1000 1000 7 8 2 0 true). Time Qed.

Lemma nonhalt40: ~halts (TM_from_str "1RB0LB3LA2RA---_2LA3RB1LB4RA3LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 2 2 0 0). Time Qed.

Lemma nonhalt41: ~halts (TM_from_str "1RB3LA4LA1RA1LA_2LA3RB3RB2LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt42: ~halts (TM_from_str "1RB3RA0LB1LA---_2LA4LB4RB3LA1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt43: ~halts (TM_from_str "1RB3RB1LA4LA3RA_2LA---3LA1LA4RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt44: ~halts (TM_from_str "1RB2LB4LB4RA2RB_2LA---3RB0RA3LA") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt45: ~halts (TM_from_str "1RB2RB3LB2RA2RA_2LA---3LA4RB0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 0 16 0 0). Time Qed.

Lemma nonhalt46: ~halts (TM_from_str "1RB2LA1RA4LA0LB_1LA3LA2RB---4RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt47: ~halts (TM_from_str "1RB2LA4LA1LB2RA_1LA4RB3RB---1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt48: ~halts (TM_from_str "1RB2LA1RA4LA0LB_1LA3LA2RB---2LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt49: ~halts (TM_from_str "1RB2RB4LA4RA3LA_1LA3RB---1LB1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt50: ~halts (TM_from_str "1RB4RB1LA4RA3RB_1LB2RB3LA0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt51: ~halts (TM_from_str "1RB0RB1LB2RA---_2LA3RA3LB4LA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt52: ~halts (TM_from_str "1RB3RB---4LA3RA_2LA4RB3LA1RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 4 16 0). Time Qed.

Lemma nonhalt53: ~halts (TM_from_str "1RB2LB1RB---3RA_2LA4RB3RA1LB2LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt54: ~halts (TM_from_str "1RB3LB4LB0LB---_2LA0LA2RB1RB3RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 21 3200 2 2 1 0). Time Qed.

Lemma nonhalt55: ~halts (TM_from_str "1RB3RA4RB---0LB_2LA0LB4RA1LA4RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 21 3200 2 2 1 0). Time Qed.

Lemma nonhalt56: ~halts (TM_from_str "1RB3LB1LA2RA0RB_2LA3RA4LB3RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 20 3200 2 3 1 0). Time Qed.

Lemma nonhalt57: ~halts (TM_from_str "1RB3LB4LA2RA1RB_2LA2LA1RA---3LB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 6 3200 0 3 0 0). Time Qed.

Lemma nonhalt58: ~halts (TM_from_str "1RB3LA4RA---0LB_2LA4RB0RA0LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 1 2 0). Time Qed.

Lemma nonhalt59: ~halts (TM_from_str "1RB3LA1RB0LA1RA_2LA---4LA4RB---") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt60: ~halts (TM_from_str "1RB2LB4LA2RB0RA_1LA3RA0RB---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 1 3200 0 2 1 0). Time Qed.

Lemma nonhalt61: ~halts (TM_from_str "1RB2LB4LA2RA2RB_2LA---3RB2LB3LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 5 1 0). Time Qed.

Lemma nonhalt62: ~halts (TM_from_str "1RB3LA1RB0LB1RA_2LA3LA4LA4RB---") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt63: ~halts (TM_from_str "1RB4RA3RB4RB0LA_2LB1RA---1LA3LA") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt64: ~halts (TM_from_str "1RB3LA1RB0LA1RA_2LA---4LB4RB1RA") c0.
Proof. solve_cert (NG 0 1000 1000 2 24 0 0 false). Time Qed.

Lemma nonhalt65: ~halts (TM_from_str "1RB2RA1LA4RB1LB_2LA3LA1LB0RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 1 2 0). Time Qed.

Lemma nonhalt66: ~halts (TM_from_str "1RB2LB4LA2RA0RA_1LA3RA0RB---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 1 3200 0 2 1 0). Time Qed.

Lemma nonhalt67: ~halts (TM_from_str "1RB3RB---4RB0LB_2LA0RA1LB4RA3LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 20 3200 2 5 1 0). Time Qed.

Lemma nonhalt68: ~halts (TM_from_str "1RB2RA0LB4LB3RA_2LA---3LA4LA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 20 3200 2 5 1 0). Time Qed.

Lemma nonhalt69: ~halts (TM_from_str "1RB3LB4LB1LA2RB_2LA0RA4RA---1LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 10 3200 2 4 0 0). Time Qed.

Lemma nonhalt70: ~halts (TM_from_str "1RB3RB---4LA0RA_2LA3RA1LA3LB0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 10 3200 2 1 1 0). Time Qed.

Lemma nonhalt71: ~halts (TM_from_str "1RB3RA1LB0LB3RA_2LA4RB---1LA0LB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 1 4 1 0). Time Qed.

Lemma nonhalt72: ~halts (TM_from_str "1RB1RA3LB---3LB_1LB2LA0RB4RB3LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 0 16 0 0). Time Qed.

Lemma nonhalt73: ~halts (TM_from_str "1RB3RA1RA4RB1LA_2LB3LA1LA3RA---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 12 3200 1 5 0 0). Time Qed.

Lemma nonhalt74: ~halts (TM_from_str "1RB3RB---3LB0LB_2LA3RB1LA4RB2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 10 3200 2 1 1 0). Time Qed.

Lemma nonhalt75: ~halts (TM_from_str "1RB3RB---3LA1RB_2LA4RA3LA4LA1LB") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt76: ~halts (TM_from_str "1RB0LB0RA---1RA_2LA4LB3RA1RB1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt77: ~halts (TM_from_str "1RB3RA1LB0LB3RA_2LA4RB---1LA2LA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 1 4 1 0). Time Qed.

Lemma nonhalt78: ~halts (TM_from_str "1RB3LA---4LA3RB_2LA4RB1RB1LB3RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 1 4 1 0). Time Qed.

Lemma nonhalt79: ~halts (TM_from_str "1RB1RA3LA4LB---_1LB2LA0RB4LA3RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 0 16 0 0). Time Qed.

Lemma nonhalt80: ~halts (TM_from_str "1RB0LB4LA0RA0LB_2LA4LB3RB---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 1 2 0). Time Qed.

Lemma nonhalt81: ~halts (TM_from_str "1RB2RB3LB3RA0RA_2LA---3LA4RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 10 3200 2 1 1 0). Time Qed.

Lemma nonhalt82: ~halts (TM_from_str "1RB3LA---0RB0LB_2LA4RA1RA4RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 10 3200 2 1 1 0). Time Qed.

Lemma nonhalt83: ~halts (TM_from_str "1RB0RA3LB0RB3RB_2LA---4LA4LB2RB") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt84: ~halts (TM_from_str "1RB3LA2LA2LB0LA_2LA2RB3RB4RA---") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt85: ~halts (TM_from_str "1RB2LA3LB---0RB_1LA2RB1RA4LB3LB") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt86: ~halts (TM_from_str "1RB2LA0RB4LA0LA_1LA3LA1RA0LB---") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt87: ~halts (TM_from_str "1RB3RB---3LA1RB_2LA0RA3LA4LA1LB") c0.
Proof. solve_cert (NG 0 1000 1000 6 0 0 0 true). Time Qed.

Lemma nonhalt88: ~halts (TM_from_str "1RB0RB4RB---2LB_2LB3RA4RA0LA1LB") c0.
Proof. solve_cert (NG 0 1000 1000 1 0 6 0 true). Time Qed.

Lemma nonhalt89: ~halts (TM_from_str "1RB2LA3LA3RB---_1LB2RA4RB0LB3RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 10 3200 2 1 1 0). Time Qed.

Lemma nonhalt90: ~halts (TM_from_str "1RB2LB4RB0RA3LA_2LA0LB3RA0LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 21 3200 2 2 1 0). Time Qed.

Lemma nonhalt91: ~halts (TM_from_str "1RB3LA3LA0RA1LA_2LA4RA4LA0LB---") c0.
Proof. solve_cert (NG 0 1000 1000 3 8 2 0 true). Time Qed.

Lemma nonhalt92: ~halts (TM_from_str "1RB1RB---2LA2LA_2LB3RB1LA4LB4RA") c0.
Proof. solve_cert (NG 0 1000 1000 1 1 6 0 true). Time Qed.

Lemma nonhalt93: ~halts (TM_from_str "1RB2RB4RA1LB2LA_1LA3RB0LA0LA---") c0.
Proof. solve_cert (NG 0 1000 1000 4 0 4 0 true). Time Qed.

Lemma nonhalt94: ~halts (TM_from_str "1RB3LB0RA3LB2RB_2LA3LA4LB0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 21 3200 2 2 1 0). Time Qed.

Lemma nonhalt95: ~halts (TM_from_str "1RB2RB4RA1LB3LA_1LA3RB0LA0LA---") c0.
Proof. solve_cert (NG 0 1000 1000 4 0 4 0 true). Time Qed.

Lemma nonhalt96: ~halts (TM_from_str "1RB2LA3LB4LA2RA_0LA---3RA4RB1RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 19 3200 2 6 1 0). Time Qed.

Lemma nonhalt97: ~halts (TM_from_str "1RB3RA2LA4LA2LB_2LA2RB4RB---0LA") c0.
Proof. solve_cert (NG 0 1000 1000 4 0 4 0 true). Time Qed.

Lemma nonhalt98: ~halts (TM_from_str "1RB3LA4RA---1LA_2LA0RB4LB2LB2RB") c0.
Proof. solve_cert (NG 0 1000 1000 3 8 2 0 true). Time Qed.

Lemma nonhalt99: ~halts (TM_from_str "1RB1LA0RB4LB2LA_2LA3RA4RA---0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 21 3200 2 2 1 0). Time Qed.

Lemma nonhalt100: ~halts (TM_from_str "1RB3LB0LB2RB---_2LA3RA1LB4LA3RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 1 2 0 0). Time Qed.

Lemma nonhalt101: ~halts (TM_from_str "1RB3LA1RA0RB1LA_2LA0LB4RB1RA---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 8 3200 1 2 0 0). Time Qed.

Lemma nonhalt102: ~halts (TM_from_str "1RB0LB0RA4RA---_2LA4RA3RA0LB3LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt103: ~halts (TM_from_str "1RB3LA0LB3RA2RA_2LA---4LB4RB1RB") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt104: ~halts (TM_from_str "1RB3RA0LB4LB3RB_2LA1RB---4LA1RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt105: ~halts (TM_from_str "1RB3LB0LB4RB2RA_2LA3LA1RB1RA---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt106: ~halts (TM_from_str "1RB2LA---4LA1LB_2LA0RA3RB3LB4RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt107: ~halts (TM_from_str "1RB3LA1LA0RA2RA_2LA2RA4LA0LB---") c0.
Proof. solve_cert (NG 0 1000 1000 3 6 4 0 true). Time Qed.

Lemma nonhalt108: ~halts (TM_from_str "1RB3LA4LA0RB0RA_1LB2LA0LA1RA---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 3 3200 1 2 0 0). Time Qed.

Lemma nonhalt109: ~halts (TM_from_str "1RB2LA0RB4RA0LA_1LA3LB1RA1LB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 7 3200 2 1 1 0). Time Qed.

Lemma nonhalt110: ~halts (TM_from_str "1RB2LB2LA0RA---_2LA0LA3RA4LB2LA") c0.
Proof. solve_cert (NG 0 1000 1000 2 16 0 0 false). Time Qed.

Lemma nonhalt111: ~halts (TM_from_str "1RB2LB2LA0RA---_2LA0LA3RA4LB2RA") c0.
Proof. solve_cert (NG 0 1000 1000 2 12 6 0 true). Time Qed.

Lemma nonhalt112: ~halts (TM_from_str "1RB3LA2LB0LB2RB_2LA---3RA4RA4LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 17 3200 2 2 1 0). Time Qed.

Lemma nonhalt113: ~halts (TM_from_str "1RB3LB4LA0RB---_2LA2RA3RA2LB0LB") c0.
Proof. solve_cert (NG 0 1000 1000 1 2 0 0 true). Time Qed.

Lemma nonhalt114: ~halts (TM_from_str "1RB0LB3LA2RA---_2LA4RA3RA1LB3LB") c0.
Proof. solve_cert (NG 0 1000 1000 1 2 0 0 true). Time Qed.

Lemma nonhalt115: ~halts (TM_from_str "1RB3LB4LB2RA3RA_2LA3RB0RA1LB---") c0.
Proof. solve_cert (NG 0 1000 1000 1 2 0 0 true). Time Qed.

Lemma nonhalt116: ~halts (TM_from_str "1RB2LB3LB1LB0LA_2LA4RB1RA0RA---") c0.
Proof. solve_cert (NG 0 1000 1000 1 2 0 0 true). Time Qed.

Lemma nonhalt117: ~halts (TM_from_str "1RB2LA3RA4LB0LB_1LA2RA1RB0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 2 1 0). Time Qed.

Lemma nonhalt118: ~halts (TM_from_str "1RB3LA3LB0LA1RA_2LA4RA4LA4RB---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 2 1 0). Time Qed.

Lemma nonhalt119: ~halts (TM_from_str "1RB2LB1LA0LB---_1LA2RB3LB4RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 8 3200 2 2 1 0). Time Qed.

Lemma nonhalt120: ~halts (TM_from_str "1RB2LA4LA---1RB_2LA0RB3LB2RB1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 4 3200 2 1 2 0). Time Qed.

Lemma nonhalt121: ~halts (TM_from_str "1RB3LB0RA4LA3RA_2LA---3RB2RA2LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 2 1 0). Time Qed.

Lemma nonhalt122: ~halts (TM_from_str "1RB3RA3LB4RB---_2LA2RB1RB1LA2RB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 2 1 0). Time Qed.

Lemma nonhalt123: ~halts (TM_from_str "1RB2RB4LA1LA1LB_2LA4RA3RB---0RB") c0.
Proof. solve_cert (NG 0 1000 1000 3 12 0 0 false). Time Qed.

Lemma nonhalt124: ~halts (TM_from_str "1RB2LB4RB---2RA_2LA3LA0LB0RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 7 3200 2 1 2 0). Time Qed.

Lemma nonhalt125: ~halts (TM_from_str "1RB0LA3LA0LB0RA_2LB2LA3RA4RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 1 1 0). Time Qed.

Lemma nonhalt126: ~halts (TM_from_str "1RB0LA3RB0RB0LB_2LB1RA4RA1LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 1 1 0). Time Qed.

Lemma nonhalt127: ~halts (TM_from_str "1RB2LA4LB3LA2RB_2LA---3RB4RA0RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 12 3200 2 1 1 0). Time Qed.

Lemma nonhalt128: ~halts (TM_from_str "1RB3LB1LB2RA0LA_2LA0RA1RB4LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 16 3200 2 1 1 0). Time Qed.

Lemma nonhalt129: ~halts (TM_from_str "1RB3LA---1LB1RB_2LA0LB3RA4RB3LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 16 3200 2 1 1 0). Time Qed.

Lemma nonhalt130: ~halts (TM_from_str "1RB3RA0LA1LA1RA_2LA3LB4RB2RB---") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 3 3200 0 2 0 0). Time Qed.

Lemma nonhalt131: ~halts (TM_from_str "1RB---0RB4LA0LB_2LB3LA3RA4RB4RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 2 14 0 0). Time Qed.

Lemma nonhalt132: ~halts (TM_from_str "1RB0RA3RB0LB2LB_2LA4LA1RA---1LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 14 3200 2 1 1 0). Time Qed.

Lemma nonhalt133: ~halts (TM_from_str "1RB4LA0RB0LA---_2LB2LA3RA3LA2RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 0 7 1 0). Time Qed.

Lemma nonhalt134: ~halts (TM_from_str "1RB0LB0RA4RA---_2LA2LB3RA0LB3LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt135: ~halts (TM_from_str "1RB3LB1LB0RA3LA_2LA3LA1RA4RA---") c0.
Proof. solve_cert (NG 0 1000 1000 3 0 6 0 true). Time Qed.

Lemma nonhalt136: ~halts (TM_from_str "1RB3LB1LB0RA3RA_2LA3LA1RA4LA---") c0.
Proof. solve_cert (NG 0 1000 1000 3 0 6 0 true). Time Qed.

Lemma nonhalt137: ~halts (TM_from_str "1RB2RB3RB---1LB_1LA3LA3LB4RB0RB") c0.
Proof. solve_cert (NG 0 1000 1000 2 12 2 0 true). Time Qed.

Lemma nonhalt138: ~halts (TM_from_str "1RB4LA4LA1LA0RB_1LB2LA3RA---2RA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 2 3200 2 1 3 0). Time Qed.

Lemma nonhalt139: ~halts (TM_from_str "1RB3LB3LA4RA2LA_2LA1LB0RB0RA---") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt140: ~halts (TM_from_str "1RB3RA0LA1LA2LB_2LA4RB1RB---2LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt141: ~halts (TM_from_str "1RB3LA0LA2RB2RA_2LA3RB1LB4RA---") c0.
Proof. solve_cert (NG 0 1000 1000 1 8 0 0 true). Time Qed.

Lemma nonhalt142: ~halts (TM_from_str "1RB2LB0RA---2RB_2LA4RB3LB1RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 6 3200 2 1 1 0). Time Qed.

Lemma nonhalt143: ~halts (TM_from_str "1RB3RA4LA2LA2RB_2LA0LB1RA---1LA") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 6 3200 2 1 1 0). Time Qed.

Lemma nonhalt144: ~halts (TM_from_str "1RB0LB4LA2RA1RA_2LA3RB1LB---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 1000 1000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt145: ~halts (TM_from_str "1RB0LB0RA2LB---_2LA4RA3RA0LB3LB") c0.
Proof. solve_cert (RWL_mod 1001 1000 1000 1 3200 2 2 8 0). Time Qed.

Lemma nonhalt146: ~halts (TM_from_str "1RB3RA---4RB0LB_2LB1RB3LA1LA2LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 12 0 0). Time Qed.

Lemma nonhalt147: ~halts (TM_from_str "1RB3RA1LA2RB3LA_2LA4LA---2RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 14 3200 2 3 1 0). Time Qed.

Lemma nonhalt148: ~halts (TM_from_str "1RB0LB1LA2RA4RA_2LA4LA3LB---0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 18 3200 2 4 2 0). Time Qed.

Lemma nonhalt149: ~halts (TM_from_str "1RB4LA0LA3LA---_1LB2RB3RA0RB2RA") c0.
Proof. solve_cert (NG 0 3000 3000 8 8 0 0 true). Time Qed.

Lemma nonhalt150: ~halts (TM_from_str "1RB2RB1LA2RA0RA_2LB3LA4LB3RA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt151: ~halts (TM_from_str "1RB2LA0LB4RB---_1LA2RA3RB1RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt152: ~halts (TM_from_str "1RB2RB---4LA1LA_2LA3RB1LB4RB3LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 3 3200 2 1 2 0). Time Qed.

Lemma nonhalt153: ~halts (TM_from_str "1RB2LA0RB---4LA_1LA3LA1RA4RB0LA") c0.
Proof. solve_cert (NG 0 3000 3000 3 2 0 0 true). Time Qed.

Lemma nonhalt154: ~halts (TM_from_str "1RB3LB---0RB3RA_1LB2LA3RA4LB1RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt155: ~halts (TM_from_str "1RB2RA2LB3LA0RB_2LA4LA3RB0RA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt156: ~halts (TM_from_str "1RB2LB0LB0RA---_2LA3LB1RB4RB1RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt157: ~halts (TM_from_str "1RB4RA3RB1LA0LA_2LB3RA1LB4LA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 5 3200 1 13 2 0). Time Qed.

Lemma nonhalt158: ~halts (TM_from_str "1RB3LA1LA4LB---_2LB2RA0RB0LB1RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 8 0 true). Time Qed.

Lemma nonhalt159: ~halts (TM_from_str "1RB4RA3LA1LA2LB_2LB2RA1RB0RB---") c0.
Proof. solve_cert (NG 0 3000 3000 4 6 8 0 true). Time Qed.

Lemma nonhalt160: ~halts (TM_from_str "1RB2LB3RA0LB---_2LA4LB2RB2LA0LA") c0.
Proof. solve_cert (NG 0 3000 3000 3 8 4 0 true). Time Qed.

Lemma nonhalt161: ~halts (TM_from_str "1RB3LA1LA4RA1LB_2LB2RA0RA0LB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt162: ~halts (TM_from_str "1RB3LA3RB0LA0RA_2LA4LB4LB3RA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt163: ~halts (TM_from_str "1RB2RB1LA4LB---_2LB2RA3LA0RB3RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt164: ~halts (TM_from_str "1RB3LB3RA3RA0RA_2LA4RA4RB0LA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt165: ~halts (TM_from_str "1RB2LB---4LA0RB_1LA3RB0RA4RB1LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt166: ~halts (TM_from_str "1RB2RB0LA3LB0LA_2LA4RB3RB0RB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt167: ~halts (TM_from_str "1RB2LB4LB0RA---_2LA2RA3RB0LB2RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt168: ~halts (TM_from_str "1RB2RB4LA2RA1LA_2LB3LA---3LA1RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt169: ~halts (TM_from_str "1RB3RA1LB2RA1LA_2LA---4RA4LB3LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt170: ~halts (TM_from_str "1RB3LA3LB---0RB_2LA4LB4RA0LB4LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt171: ~halts (TM_from_str "1RB1LA4RA1RB0RB_2LA3LB1RA0RA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt172: ~halts (TM_from_str "1RB2RB4RB4LA---_2LA4LB3RB0RB2LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt173: ~halts (TM_from_str "1RB3LA4LA2RB0LB_2LB1LA---1RA3RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt174: ~halts (TM_from_str "1RB3LA4LA2RA3LB_2LA---4RA0RA3RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt175: ~halts (TM_from_str "1RB3LA4RB0LB---_2LA1RA1LB3RB0LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt176: ~halts (TM_from_str "1RB3LA---4LA3RB_1LB2LA3RB4RA0LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt177: ~halts (TM_from_str "1RB3LB4RA1LA---_2LA3RA1RB0LB2RB") c0.
Proof. solve_cert (NG 0 3000 3000 4 6 8 0 true). Time Qed.

Lemma nonhalt178: ~halts (TM_from_str "1RB0LB---4LB2RB_2LA4LA3RB0RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt179: ~halts (TM_from_str "1RB0LB2LB---1LB_2LA2RA3RA4RB0RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt180: ~halts (TM_from_str "1RB3LA4LA0LA---_2LA0RB1LA3RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt181: ~halts (TM_from_str "1RB2LA4LA0RA3LB_2LA3RA0LB---1RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt182: ~halts (TM_from_str "1RB3LA1LA4RA0LB_2LB2RA2RA4LB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt183: ~halts (TM_from_str "1RB3LA1LB4LB2RB_2LA3RA1RB2LB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt184: ~halts (TM_from_str "1RB2LB0RA3LA0RB_1LA3RA4LB0LA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt185: ~halts (TM_from_str "1RB2RA3LA4LA2RB_2LA1RB---0RA1LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 8 0 true). Time Qed.

Lemma nonhalt186: ~halts (TM_from_str "1RB2LA3LA1RA0LB_1LA4RA3RB0LA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt187: ~halts (TM_from_str "1RB2LB1LA4RA3LB_2LA0LA3RB0RB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt188: ~halts (TM_from_str "1RB3LA1LB4RB---_2LA3RA1RB2LB0LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt189: ~halts (TM_from_str "1RB3LA3RB0LA0RA_2LA2LA4LB3RA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt190: ~halts (TM_from_str "1RB3LB---4LA4RB_2LA0RB0RA0LB3RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt191: ~halts (TM_from_str "1RB4RA3LA4LB3RA_2LB3LA---1RA0LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 12 0 0). Time Qed.

Lemma nonhalt192: ~halts (TM_from_str "1RB3LA1LA0RB---_2LA0LA4LA1RA2RA") c0.
Proof. solve_cert (NG 0 3000 3000 3 8 4 0 true). Time Qed.

Lemma nonhalt193: ~halts (TM_from_str "1RB3LB0LB2RB---_2LA3RA4RA1LA3RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 14 3200 2 3 1 0). Time Qed.

Lemma nonhalt194: ~halts (TM_from_str "1RB3RB4LA---2RA_2LB2LA0LA4RB3LB") c0.
Proof. solve_cert (NG 0 3000 3000 3 8 4 0 true). Time Qed.

Lemma nonhalt195: ~halts (TM_from_str "1RB0LB---3LB---_2LA4RA3RB0RB3LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt196: ~halts (TM_from_str "1RB2LA0RB4LA0RA_2LB1LA3RA---2LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 12 0 0). Time Qed.

Lemma nonhalt197: ~halts (TM_from_str "1RB---4RA0LB3LB_2LB3LA4LB0RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 6 0 true). Time Qed.

Lemma nonhalt198: ~halts (TM_from_str "1RB3LA3RB2LA1LA_2LA2RA4RA2LB---") c0.
Proof. solve_cert (NG 0 3000 3000 4 32 0 0 false). Time Qed.

Lemma nonhalt199: ~halts (TM_from_str "1RB2RB3LA---4LB_0LA2LB4LB4RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 6 4 6 0 true). Time Qed.

Lemma nonhalt200: ~halts (TM_from_str "1RB3RA0LA4LA0RB_2LB1LA4RB---2RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt201: ~halts (TM_from_str "1RB3LB0LB2RB---_2LA3RA4RA1LA3LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt202: ~halts (TM_from_str "1RB3RA4LB0LB2RB_2LA---2RB4RA3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 5 1 0). Time Qed.

Lemma nonhalt203: ~halts (TM_from_str "1RB0LB---1RA3LA_2LA4RA3RA0LB4LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt204: ~halts (TM_from_str "1RB2RB4LA1LB---_2LA2LB3RB0RB3RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 16 3200 0 6 0 0). Time Qed.

Lemma nonhalt205: ~halts (TM_from_str "1RB3LB4LB4LA2RB_2LA0RA4RA---1LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 14 3200 2 3 1 0). Time Qed.

Lemma nonhalt206: ~halts (TM_from_str "1RB0LA3RB---0LB_2LB2LA0RA4LB4RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 9 3200 2 5 2 0). Time Qed.

Lemma nonhalt207: ~halts (TM_from_str "1RB3LA4RA0RB0LA_2LB2LA0LA0RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 9 3200 2 5 2 0). Time Qed.

Lemma nonhalt208: ~halts (TM_from_str "1RB0RB2LB0LB---_1LA2RB3RB4RA0LA") c0.
Proof. solve_cert (NG 0 3000 3000 8 12 0 0 false). Time Qed.

Lemma nonhalt209: ~halts (TM_from_str "1RB2LB3LA1LA1RA_1LA2RB0RA4LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt210: ~halts (TM_from_str "1RB3RA2LB1LA0RB_2LA4LA---3LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 15 1 0). Time Qed.

Lemma nonhalt211: ~halts (TM_from_str "1RB2RB1LA2RA0LB_2LB3LA4RA3RA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt212: ~halts (TM_from_str "1RB3LB4LB4RA2RB_2LA0RA4RA---1LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt213: ~halts (TM_from_str "1RB2LA0LB4LA---_1LA2RA3RB1LB3RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 4 6 0). Time Qed.

Lemma nonhalt214: ~halts (TM_from_str "1RB2RA3LA4LA3RA_2LA---1LA4RB2RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 8 4 0 true). Time Qed.

Lemma nonhalt215: ~halts (TM_from_str "1RB2LB3RB4LB---_2LA2RA3RA0LB3RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt216: ~halts (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4RB0RA") c0.
Proof. solve_cert (NG 0 3000 3000 1 6 2 0 true). Time Qed.

Lemma nonhalt217: ~halts (TM_from_str "1RB4LA0RB2RA---_2LB3RB1LB1LA2RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 17 3200 0 3 0 0). Time Qed.

Lemma nonhalt218: ~halts (TM_from_str "1RB4RB3LA0LB---_2LB2LA1RA3RA0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 14 3200 2 3 1 0). Time Qed.

Lemma nonhalt219: ~halts (TM_from_str "1RB3LA1RA0LA3LB_2LA4RB1LA2RA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt220: ~halts (TM_from_str "1RB4RB3LA4LA3LA_2LB3RA---1RA1LA") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt221: ~halts (TM_from_str "1RB0LB1RA0RA---_2LA3LB3RB4RA1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 5 3200 2 1 4 0). Time Qed.

Lemma nonhalt222: ~halts (TM_from_str "1RB2RB4LA1LA2RA_1LA3RB---4RB3LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 4 6 0). Time Qed.

Lemma nonhalt223: ~halts (TM_from_str "1RB4RB3RA0LA---_2LB3LA0RB1RA3RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt224: ~halts (TM_from_str "1RB2LA4LA1RA0LB_1LA3LA3RB---0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt225: ~halts (TM_from_str "1RB2RB3LA2RA---_2LA4RB3RB2LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 4 6 0). Time Qed.

Lemma nonhalt226: ~halts (TM_from_str "1RB3LA---4LB1LA_2LA0LB4RA4RB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt227: ~halts (TM_from_str "1RB3LB4LB2RA0RB_2LA1LB0RA0LB---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 2 4 0 0). Time Qed.

Lemma nonhalt228: ~halts (TM_from_str "1RB2LA4LA---2RA_1LA3LA1RB4RB3LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 4 6 0). Time Qed.

Lemma nonhalt229: ~halts (TM_from_str "1RB0LB1RA4LA0LA_2LA4RB3RA2RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt230: ~halts (TM_from_str "1RB3LA---0LB4RA_2LA1RA4LB4RB1LA") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt231: ~halts (TM_from_str "1RB4RB3LA0RB2LA_1LB2LA2RB4RA---") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt232: ~halts (TM_from_str "1RB3LA2RB0RA1RA_2LA1LB1LA4RA---") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt233: ~halts (TM_from_str "1RB2RB3LA4LA3LA_2LB3RA---1RA1LA") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt234: ~halts (TM_from_str "1RB2LA1LA4RB2LB_0LA3RA0LB---2RA") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt235: ~halts (TM_from_str "1RB2LB3RB4RB---_2LA2RA3RA0LB3LB") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt236: ~halts (TM_from_str "1RB4RB3LA2LA3LA_2LB3RA1LA1RA---") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt237: ~halts (TM_from_str "1RB3LA3LA0RB---_2LB1LA4LB2RA1RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 6 8 0 true). Time Qed.

Lemma nonhalt238: ~halts (TM_from_str "1RB3RA0LB4RB3LA_2LA---4RB2RB2RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 7 0 0). Time Qed.

Lemma nonhalt239: ~halts (TM_from_str "1RB1LB0LB3LA2LB_2LA4RB3RB2RB---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 7 0 0). Time Qed.

Lemma nonhalt240: ~halts (TM_from_str "1RB2RB4LA2LB0RB_2LA---3RB0LA4RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 2 0 0 true). Time Qed.

Lemma nonhalt241: ~halts (TM_from_str "1RB3LA4RB2RB1LA_1LB2LA2RA1RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 3 3200 2 1 6 0). Time Qed.

Lemma nonhalt242: ~halts (TM_from_str "1RB3LB1LB---1RA_2LA4LA4RB2RB1RB") c0.
Proof. solve_cert (NG 0 3000 3000 4 32 0 0 false). Time Qed.

Lemma nonhalt243: ~halts (TM_from_str "1RB3RA1LB---4LB_2LA4RB0LA4LB0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 8 3200 2 2 4 0). Time Qed.

Lemma nonhalt244: ~halts (TM_from_str "1RB---4LB4LA2RA_2LB3LA1RA4RA0LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 3 1 0). Time Qed.

Lemma nonhalt245: ~halts (TM_from_str "1RB3RA3RB4LB0LA_2LA---2RA0LA4RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 9 3200 2 1 8 0). Time Qed.

Lemma nonhalt246: ~halts (TM_from_str "1RB2LA---0RB4LB_2LA3LA3LB4RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt247: ~halts (TM_from_str "1RB0LB3RA2LB2RA_2LA4RA2RB0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt248: ~halts (TM_from_str "1RB0LB4RA1LB---_2LA3RB1RA0LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt249: ~halts (TM_from_str "1RB3RA0LA4LA3RB_2LB3LA---2RA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt250: ~halts (TM_from_str "1RB3RA3LA4LA3RB_2LB3LA---2LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt251: ~halts (TM_from_str "1RB3RB---2RB0LB_2LA4RB1LB3RA1LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt252: ~halts (TM_from_str "1RB2RA1LA---0LB_2LA0RB3LB4RB3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt253: ~halts (TM_from_str "1RB3RA1LA4LA3RB_0LB2LA0LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt254: ~halts (TM_from_str "1RB2LA---4RB1LB_2LA0RA3LB4RA3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt255: ~halts (TM_from_str "1RB3RB---4LB2LA_2LA0RA1LB4LA3RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt256: ~halts (TM_from_str "1RB2LA3RB1LB---_2LA0RA2LB4LA3RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt257: ~halts (TM_from_str "1RB2RA3LA4RB3LA_0LB2LA0LA0RA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt258: ~halts (TM_from_str "1RB2RA4LA2LA2RB_0LB2LA3LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt259: ~halts (TM_from_str "1RB2RA4LA2LA2RB_2LB3RB3LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt260: ~halts (TM_from_str "1RB0RB3LA1LA0LB_2LA4RB3RB2RB---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt261: ~halts (TM_from_str "1RB0RA3RB0LB---_2LA1RB4LB4LA3RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt262: ~halts (TM_from_str "1RB1LA3LB2RB---_2LA3RA4LA1LA3LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 0 12 0 0). Time Qed.

Lemma nonhalt263: ~halts (TM_from_str "1RB1LA2LA4RA2LB_1LA2RB3RB0LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt264: ~halts (TM_from_str "1RB2LA4RA2LB0RB_0LA3LA3RA0LA---") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 3 3200 1 2 0 0). Time Qed.

Lemma nonhalt265: ~halts (TM_from_str "1RB2RA3LA0LA---_2LB1LA4LA0RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 6 1 0). Time Qed.

Lemma nonhalt266: ~halts (TM_from_str "1RB3RA4RB---1LB_2LA1LA4RB4LB0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt267: ~halts (TM_from_str "1RB2LA3LA4LB0RB_1LA0LA2RA0RA---") c0.
Proof. solve_cert (NG 0 3000 3000 4 32 0 0 false). Time Qed.

Lemma nonhalt268: ~halts (TM_from_str "1RB2LA4LB4RA0RA_1LA3LA3RB---4LA") c0.
Proof. solve_cert (NG 0 3000 3000 4 32 0 0 false). Time Qed.

Lemma nonhalt269: ~halts (TM_from_str "1RB0RB---0LB1LB_2LA4RA3LB4LB3RA") c0.
Proof. solve_cert (NG 0 3000 3000 3 4 0 0 false). Time Qed.

Lemma nonhalt270: ~halts (TM_from_str "1RB3RB4LB2LA0RB_2LA3RA1LA2RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 4 3200 2 1 3 0). Time Qed.

Lemma nonhalt271: ~halts (TM_from_str "1RB2LB3LA0RB0RA_2LA4LB0RA2RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt272: ~halts (TM_from_str "1RB3LB0LA---1RA_2LA3RB4RB4LB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 3 3200 1 15 0 0). Time Qed.

Lemma nonhalt273: ~halts (TM_from_str "1RB3RB---3LB3RA_2LA4RB4LB1LA0LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt274: ~halts (TM_from_str "1RB3RA3LA0RB2RB_2LA---4LA4LB4RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt275: ~halts (TM_from_str "1RB3LB4LA0RB---_2LA1RA1LB2RA0LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt276: ~halts (TM_from_str "1RB3LA1LA4LB0RA_2LA2RA2RA0LB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt277: ~halts (TM_from_str "1RB3LB---0RB0LA_2LA4LA1RA4LB3RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt278: ~halts (TM_from_str "1RB3LA0LA0LB3RA_2LA2RA4RB1RB---") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt279: ~halts (TM_from_str "1RB3LB4LB4RA---_2LA1LB0RA0LB0RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt280: ~halts (TM_from_str "1RB3LB2RA4RB1LA_2LA0LB0RA---2RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt281: ~halts (TM_from_str "1RB3LA1LB---2LA_2LA0RB4RB4LB0RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt282: ~halts (TM_from_str "1RB4RB3RA0LA---_2LB3LA1LB1RA3RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt283: ~halts (TM_from_str "1RB1LB1LB0RA---_2LA2RB3RB4RA0LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt284: ~halts (TM_from_str "1RB2LB4RB0LB---_1LA3RB3LB2RA2LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 24 0 0 false). Time Qed.

Lemma nonhalt285: ~halts (TM_from_str "1RB2LA3LA0RB---_1LA1RB2RB4LB2RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt286: ~halts (TM_from_str "1RB3LA4LB1RA0RA_0LB2LA3LA2RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt287: ~halts (TM_from_str "1RB2LA1RA4LB0RA_0LA3LA3RA2LA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt288: ~halts (TM_from_str "1RB4RA0RB2LA0LA_1LB2LA3RB4RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 3 2 0). Time Qed.

Lemma nonhalt289: ~halts (TM_from_str "1RB2RB4LB2LA---_2LA4RA3RB1LA0LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 0 2 0 0). Time Qed.

Lemma nonhalt290: ~halts (TM_from_str "1RB3LB4LA0LA4RB_2LA2RA0RA---1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt291: ~halts (TM_from_str "1RB1LB0LB2RB---_2LA4RA3LB2RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 12 0). Time Qed.

Lemma nonhalt292: ~halts (TM_from_str "1RB3LB4LA1LA---_2LA2LB0RA4RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt293: ~halts (TM_from_str "1RB4LB0RB---0LA_2LB3LA1LB4RA2RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 12 3200 2 5 2 0). Time Qed.

Lemma nonhalt294: ~halts (TM_from_str "1RB0LB---4RB3LB_2LA4RA3LB4RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 12 0). Time Qed.

Lemma nonhalt295: ~halts (TM_from_str "1RB0LB0LA0RB---_2LA4LA3LB2RA1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 12 0). Time Qed.

Lemma nonhalt296: ~halts (TM_from_str "1RB---4RA4LB3LB_2LB3LA4LB0RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 1 1 4 0 true). Time Qed.

Lemma nonhalt297: ~halts (TM_from_str "1RB3LA0LB---2RB_2LA0RA4LB4RB1RA") c0.
Proof. solve_cert (NG 0 3000 3000 4 6 8 0 true). Time Qed.

Lemma nonhalt298: ~halts (TM_from_str "1RB2RA1LA0RA---_2LA2LB3RB4LB0LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 14 3200 2 3 1 0). Time Qed.

Lemma nonhalt299: ~halts (TM_from_str "1RB3LA1RA2LB0LB_2LA4RA---0RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 16 3200 2 4 1 0). Time Qed.

Lemma nonhalt300: ~halts (TM_from_str "1RB2LB4RA4LA2LA_2LA---3RB2RB3LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 8 0 0 false). Time Qed.

Lemma nonhalt301: ~halts (TM_from_str "1RB2RA3LA---0RB_2LA1LB4RA0LB1LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 8 0 0 false). Time Qed.

Lemma nonhalt302: ~halts (TM_from_str "1RB3LA---1LA1RA_2LA4RB3RA4LB3RB") c0.
Proof. solve_cert (NG 0 3000 3000 2 8 0 0 false). Time Qed.

Lemma nonhalt303: ~halts (TM_from_str "1RB2RB3RA4LA1LA_2LA3RB3LA---4RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 8 0 0 false). Time Qed.

Lemma nonhalt304: ~halts (TM_from_str "1RB3RB0LB4LB4LA_2LA---4RB2LA2RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt305: ~halts (TM_from_str "1RB3LA4LB1LA---_2LA0RA3LB3RB3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt306: ~halts (TM_from_str "1RB3LA4LB1LA---_2LA0RA3RB3RB3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt307: ~halts (TM_from_str "1RB3RB3LB4LB4LA_2LA---4RB2LA2RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt308: ~halts (TM_from_str "1RB---3RB2LB1RA_0LB2LA3RA4RB1LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt309: ~halts (TM_from_str "1RB2LA4LA4LB2RB_2LA---3RB0RA2RA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 10 3200 0 5 1 0). Time Qed.

Lemma nonhalt310: ~halts (TM_from_str "1RB0LB1LA2RA1RB_2LA3LA1RA4RB---") c0.
Proof. solve_cert (NG 0 3000 3000 4 8 4 0 true). Time Qed.

Lemma nonhalt311: ~halts (TM_from_str "1RB0LA3RA2LA---_2LB3RB4LB1LA1RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt312: ~halts (TM_from_str "1RB0LB4LB3LA0RA_2LA---3RA4RB---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt313: ~halts (TM_from_str "1RB3LA1RA4RA1LB_2LA3RB---0RA4LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 4 4 0). Time Qed.

Lemma nonhalt314: ~halts (TM_from_str "1RB4LA---1LB1RA_2LB3RB3LB1LA4RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 16 0 0 false). Time Qed.

Lemma nonhalt315: ~halts (TM_from_str "1RB2LA1RA4LA---_0LA3RB3LB2RB0RB") c0.
Proof. solve_cert (NG 0 3000 3000 7 0 0 0 true). Time Qed.

Lemma nonhalt316: ~halts (TM_from_str "1RB2LA3LA0RB1RA_1LA1LB2RA4RA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 0 6 0 true). Time Qed.

Lemma nonhalt317: ~halts (TM_from_str "1RB2RA3LB4RB4LA_2LA---3LA2RB2RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 1 8 0). Time Qed.

Lemma nonhalt318: ~halts (TM_from_str "1RB4LA4LA1LA0RB_2LB2LA3RA---2RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 1 4 0). Time Qed.

Lemma nonhalt319: ~halts (TM_from_str "1RB2LA3LB4RA0RA_1LA3LA1RA---2RA") c0.
Proof. solve_cert (NG 0 3000 3000 1 8 2 0 true). Time Qed.

Lemma nonhalt320: ~halts (TM_from_str "1RB3LB2RA2RB0RA_2LA4RB1LB0LA---") c0.
Proof. solve_cert (NG 0 3000 3000 2 4 4 0 true). Time Qed.

Lemma nonhalt321: ~halts (TM_from_str "1RB0LA4LA3LA---_2LB2LA3RB0RA1RA") c0.
Proof. solve_cert (NG 0 3000 3000 2 4 4 0 true). Time Qed.

Lemma nonhalt322: ~halts (TM_from_str "1RB3LA2RB0LA3RA_2LA3LA4LB2RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt323: ~halts (TM_from_str "1RB3LA1LA4RA0LA_2LA2RB3RB2LB---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt324: ~halts (TM_from_str "1RB3LA1LA1RA---_2LA2RB3RB4LB0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt325: ~halts (TM_from_str "1RB2RB4RB---0LB_2LA3LB3LA2RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt326: ~halts (TM_from_str "1RB3RB3RA1LA0LB_2LA4LA1LA---0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 22 3200 2 6 1 0). Time Qed.

Lemma nonhalt327: ~halts (TM_from_str "1RB0LA1RA4LB---_2LB3LA2RA1RB3RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 4 3 0). Time Qed.

Lemma nonhalt328: ~halts (TM_from_str "1RB2RB3LA4LA0RB_0LA---4RB2RA2LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 12 4 0 true). Time Qed.

Lemma nonhalt329: ~halts (TM_from_str "1RB4LA2RB0LA---_1LB2LA3RB0RA3LB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 9 3200 0 2 0 0). Time Qed.

Lemma nonhalt330: ~halts (TM_from_str "1RB1LA3LA0RB---_2LA2RA4LA2RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt331: ~halts (TM_from_str "1RB0RB---1LB0RA_2LB3LA3RA4RB3LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 3 4 0). Time Qed.

Lemma nonhalt332: ~halts (TM_from_str "1RB2LA3RB4LB---_0LA4LB3RA1LA0RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 3 3200 0 3 0 0). Time Qed.

Lemma nonhalt333: ~halts (TM_from_str "1RB2LA4LB4LB---_0LA4LB3RA1LA0RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 3 3200 0 3 0 0). Time Qed.

Lemma nonhalt334: ~halts (TM_from_str "1RB3RA---4LB0RB_1LB2LA3RB4RA3LB") c0.
Proof. solve_cert (NG 0 3000 3000 2 6 6 0 true). Time Qed.

Lemma nonhalt335: ~halts (TM_from_str "1RB1RA0LB1LB---_2LA2RB3RB4RA0LA") c0.
Proof. solve_cert (NG 0 3000 3000 2 6 6 0 true). Time Qed.

Lemma nonhalt336: ~halts (TM_from_str "1RB0LA3LB2RA0LB_2LB3LA---4RA1RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt337: ~halts (TM_from_str "1RB0LA1LB2RA0LB_2LB3LA---4RA0RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt338: ~halts (TM_from_str "1RB2LA3LB4LB---_2LA4LA2RB0RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt339: ~halts (TM_from_str "1RB1LA4RB0LA0LB_2LA3RA1RB4RA---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt340: ~halts (TM_from_str "1RB2LA3LB1LA---_2LA4LA2RB0RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt341: ~halts (TM_from_str "1RB3LA3LB2RA0LA_2LA4RA---4RA0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt342: ~halts (TM_from_str "1RB3LA1LB2RA0LA_2LA4RA---4RA0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt343: ~halts (TM_from_str "1RB0RB3LB4LB---_2LA4LA2RB0RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt344: ~halts (TM_from_str "1RB1RA2RA0LB---_2LB3LA3RA4RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 6 3200 2 1 1 0). Time Qed.

Lemma nonhalt345: ~halts (TM_from_str "1RB2LA0RA4LA1LB_1LA2RB3RA4RB---") c0.
Proof. solve_cert (NG 0 3000 3000 4 12 4 0 true). Time Qed.

Lemma nonhalt346: ~halts (TM_from_str "1RB1LA0LB4RB3LB_2LA3RA---1RB3LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt347: ~halts (TM_from_str "1RB2RB4LB3LA3LB_1LA3RB---4RB0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 4 3200 2 1 4 0). Time Qed.

Lemma nonhalt348: ~halts (TM_from_str "1RB3RA3LB2RA0RA_2LA---4LA4LB4RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 4 3200 2 1 4 0). Time Qed.

Lemma nonhalt349: ~halts (TM_from_str "1RB3RA4RB0LA---_2LB1LA0RB1RB3RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 6 2 0). Time Qed.

Lemma nonhalt350: ~halts (TM_from_str "1RB3RB0LB2RB4LA_2LA---4RB1RB2RB") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 2 3200 1 3 0 0). Time Qed.

Lemma nonhalt351: ~halts (TM_from_str "1RB2RA3LA1LB---_2LA3RA4RB2LB0RA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 20 3200 2 6 2 0). Time Qed.

Lemma nonhalt352: ~halts (TM_from_str "1RB4RB3RA1LA2LA_2LB2RB3LA2RA---") c0.
Proof. solve_cert (NG 0 3000 3000 1 12 0 0 true). Time Qed.

Lemma nonhalt353: ~halts (TM_from_str "1RB3LA1RA4RA0RB_2LA2RB1LB0LB---") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 10 3200 2 5 1 0). Time Qed.

Lemma nonhalt354: ~halts (TM_from_str "1RB3LA4LA0RB---_1LB2RA1RA3RB0LA") c0.
Proof. solve_cert (CPS_LRU 1001 3000 3000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt355: ~halts (TM_from_str "1RB1LA4LA4LA0RB_2LB3RA1LB---2RB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt356: ~halts (TM_from_str "1RB1LA3LA0RB3LA_2LB2RA---4RB1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt357: ~halts (TM_from_str "1RB0RB3RA2LB---_2LA4RB3RB0LA3RA") c0.
Proof. solve_cert (NG 0 3000 3000 4 0 10 1 true). Time Qed.

Lemma nonhalt358: ~halts (TM_from_str "1RB0LB1LB---2LB_2LA4RB3RA0RB4LA") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 20 3200 2 5 1 0). Time Qed.

Lemma nonhalt359: ~halts (TM_from_str "1RB3LB3RA1LB---_2LA2RA4RA0LA0LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 20 3200 2 5 1 0). Time Qed.

Lemma nonhalt360: ~halts (TM_from_str "1RB2RB4LB2LA---_1LA3RB0RA1LB1LB") c0.
Proof. solve_cert (RWL_mod 1001 3000 3000 2 3200 2 2 4 0). Time Qed.

Lemma nonhalt361: ~halts (TM_from_str "1RB4LA3RB0LB---_1LB2LA3RA0RA0RB") c0.
Proof. solve_cert (NG 0 3000 3000 3 12 6 0 true). Time Qed.

Lemma nonhalt362: ~halts (TM_from_str "1RB3LA1LA4RA2RB_2LB2LA1RA4RB---") c0.
Proof. solve_cert (NG 0 10000 10000 5 8 6 0 true). Time Qed.

Lemma nonhalt363: ~halts (TM_from_str "1RB2LA0RB4LB---_1LA3RB1RA2LB3LB") c0.
Proof. solve_cert (NG 0 10000 10000 7 16 0 0 false). Time Qed.

Lemma nonhalt364: ~halts (TM_from_str "1RB2LA3LA4RB1RA_1LB2RB2RA0LA---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 4 3200 2 1 3 0). Time Qed.

Lemma nonhalt365: ~halts (TM_from_str "1RB3LB1LA4LB---_2LA0RA2RB3RB0LA") c0.
Proof. solve_cert (NG 0 10000 10000 5 12 2 0 true). Time Qed.

Lemma nonhalt366: ~halts (TM_from_str "1RB3RA3RB2LB---_2LA4LA3RB0LA1RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 4 1 0). Time Qed.

Lemma nonhalt367: ~halts (TM_from_str "1RB1LA0LB3LA0RB_2LA2RB3RA4RA---") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 4 0 true). Time Qed.

Lemma nonhalt368: ~halts (TM_from_str "1RB4LA1LA2LA0RB_2LB3RA3RB---0RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 4 0 true). Time Qed.

Lemma nonhalt369: ~halts (TM_from_str "1RB0RB0RA0LB3RA_2LA3LA1LB4RB---") c0.
Proof. solve_cert (NG 0 10000 10000 3 8 0 0 true). Time Qed.

Lemma nonhalt370: ~halts (TM_from_str "1RB3RB---3LA3RA_2LA4RA4LB0LB1LB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 4 3200 2 2 2 0). Time Qed.

Lemma nonhalt371: ~halts (TM_from_str "1RB3RA3RB2LB---_2LA4LA3RB0LA1RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt372: ~halts (TM_from_str "1RB2LA0RB1LB3LA_1LA4RA3RA0RB---") c0.
Proof. solve_cert (NG 0 10000 10000 7 16 0 0 false). Time Qed.

Lemma nonhalt373: ~halts (TM_from_str "1RB2RA4LA1RB2RB_0LB2LA3LA---3RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt374: ~halts (TM_from_str "1RB3RA4RB---0LB_2LA2RB0RA1LB4LB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 8 3200 2 2 3 0). Time Qed.

Lemma nonhalt375: ~halts (TM_from_str "1RB3LB4LB0LA---_2LA2RB1RB0RB3RA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt376: ~halts (TM_from_str "1RB3RA4LB2RA2RB_2LA---0LB4RA3LA") c0.
Proof. solve_cert (NG 0 10000 10000 5 8 2 0 true). Time Qed.

Lemma nonhalt377: ~halts (TM_from_str "1RB2RA4LA1RB2RB_0LB2LA3LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt378: ~halts (TM_from_str "1RB1LA4RB0LA0LB_2LA3RA0LA4RA---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt379: ~halts (TM_from_str "1RB2RB3LA1RA1LA_2LB2RA---4LA3RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 24 3200 2 6 1 0). Time Qed.

Lemma nonhalt380: ~halts (TM_from_str "1RB3LB1LA0LA0RB_2LA2RB0RA4RA---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 16 3200 2 3 2 0). Time Qed.

Lemma nonhalt381: ~halts (TM_from_str "1RB4LA3LB0RB---_2LB2RA1LA1LA2LB") c0.
Proof. solve_cert (NG 0 10000 10000 5 8 2 0 true). Time Qed.

Lemma nonhalt382: ~halts (TM_from_str "1RB2LA1LA0LA3LB_2LA4RA3RA0RB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt383: ~halts (TM_from_str "1RB0LB1LA4LA---_2LA2RB3LB2RA0RB") c0.
Proof. solve_cert (NG 0 10000 10000 5 0 2 0 true). Time Qed.

Lemma nonhalt384: ~halts (TM_from_str "1RB3RA1LA1LB0LA_2LA2RB0RA4RB---") c0.
Proof. solve_cert (NG 0 10000 10000 5 0 2 0 true). Time Qed.

Lemma nonhalt385: ~halts (TM_from_str "1RB1LA4RB0LA0LB_2LA3RA1RB2RB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt386: ~halts (TM_from_str "1RB3RA---4LA3RB_2LB3LA0LB0LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt387: ~halts (TM_from_str "1RB3RA4LA4LA3RB_0LB2LA0LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt388: ~halts (TM_from_str "1RB3RA4RA4LA3RB_0LB2LA0LA---0RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt389: ~halts (TM_from_str "1RB3RA2RB2LB---_2LA4LA3RB0LA1RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt390: ~halts (TM_from_str "1RB2LB0RB---1RA_2LA3LA3LB4RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 16 0). Time Qed.

Lemma nonhalt391: ~halts (TM_from_str "1RB3RA4LB0LA---_2LA0LA2RB1LA0RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt392: ~halts (TM_from_str "1RB3RA3LA4LB0RA_2LA0RA4RA1LB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt393: ~halts (TM_from_str "1RB1LA0RB0LA2RB_2LA3RA4LB---0RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 3 0). Time Qed.

Lemma nonhalt394: ~halts (TM_from_str "1RB2LA4RB1LB0RB_1LA3RB2RB0LA---") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 1 3200 2 2 0 0). Time Qed.

Lemma nonhalt395: ~halts (TM_from_str "1RB2LA3LA4LB---_2LA3LB3RA0RB1RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 17 3200 2 6 4 0). Time Qed.

Lemma nonhalt396: ~halts (TM_from_str "1RB3LA0LA1LA1RA_2LA0LA4LA4RB---") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 10 0 true). Time Qed.

Lemma nonhalt397: ~halts (TM_from_str "1RB0LA0RB---1LB_2LB3LA4RA2RB2LB") c0.
Proof. solve_cert (NG 0 10000 10000 5 8 2 0 true). Time Qed.

Lemma nonhalt398: ~halts (TM_from_str "1RB3LA4LB2LB---_2LA3RB1RB4RA0LB") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 10 0 true). Time Qed.

Lemma nonhalt399: ~halts (TM_from_str "1RB2RA3LA4LA2RB_2LA2RA---0RA1LA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 10 0 true). Time Qed.

Lemma nonhalt400: ~halts (TM_from_str "1RB3LA1RA0RA---_2LA3LB4RB0LB2RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 10 0 true). Time Qed.

Lemma nonhalt401: ~halts (TM_from_str "1RB4LA1LA2LA0RB_2LB3RA3RB---4RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 10 0 true). Time Qed.

Lemma nonhalt402: ~halts (TM_from_str "1RB0LA4RB2LA---_2LB3RA0RB4LA3LB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 6 3 0). Time Qed.

Lemma nonhalt403: ~halts (TM_from_str "1RB3RA3RB0LA---_2LB3LA0RB4RB1LA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 6 3 0). Time Qed.

Lemma nonhalt404: ~halts (TM_from_str "1RB0LB---4RB3LB_2LA4RA3LB4LA1LA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 16 0). Time Qed.

Lemma nonhalt405: ~halts (TM_from_str "1RB2RA3RB4LA---_2LA0LB0LA0RA3LB") c0.
Proof. solve_cert (NG 0 10000 10000 3 8 0 0 true). Time Qed.

Lemma nonhalt406: ~halts (TM_from_str "1RB3RA3RB4LA0RB_2LA0LA1RA---2LB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 2 16 0). Time Qed.

Lemma nonhalt407: ~halts (TM_from_str "1RB3LA4LB---0RA_2LA2RB1LA4RB3LB") c0.
Proof. solve_cert (NG 0 10000 10000 7 16 0 0 false). Time Qed.

Lemma nonhalt408: ~halts (TM_from_str "1RB3LA1LA4LA0RB_2LA---4LA3RB3RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 2 0 true). Time Qed.

Lemma nonhalt409: ~halts (TM_from_str "1RB4LA2RB0LB---_2LB3LA1LB3RA0RA") c0.
Proof. solve_cert (NG 0 10000 10000 6 12 2 0 true). Time Qed.

Lemma nonhalt410: ~halts (TM_from_str "1RB2LA---3LA3LB_2LA2RB3RB4RB0LA") c0.
Proof. solve_cert (NG 0 10000 10000 3 12 2 0 true). Time Qed.

Lemma nonhalt411: ~halts (TM_from_str "1RB3RA4LA2RB0RA_2LA---2LB2RA3LA") c0.
Proof. solve_cert (NG 0 10000 10000 7 16 0 0 false). Time Qed.

Lemma nonhalt412: ~halts (TM_from_str "1RB0LB1LA4LB---_2LA2RB3RA0RB0LA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 8 3200 2 2 3 0). Time Qed.

Lemma nonhalt413: ~halts (TM_from_str "1RB3RA3LB4LA0LA_2LA---1RA3RB0RA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 14 3200 2 2 16 0). Time Qed.

Lemma nonhalt414: ~halts (TM_from_str "1RB2LA4LA4LB0LA_1LA3RA2RB---0RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 24 0 0 false). Time Qed.

Lemma nonhalt415: ~halts (TM_from_str "1RB0LB3RA0RA---_2LA4RA2RB1LA3RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 24 0 0 false). Time Qed.

Lemma nonhalt416: ~halts (TM_from_str "1RB4LA3LB4RA0LA_2LB3LA---1LA3RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 24 0 0 false). Time Qed.

Lemma nonhalt417: ~halts (TM_from_str "1RB1LA4LB2RB3LB_2LA3LB0RA0LB---") c0.
Proof. solve_cert (NG 0 10000 10000 3 24 0 0 false). Time Qed.

Lemma nonhalt418: ~halts (TM_from_str "1RB3RB4RA0LB---_2LA2RA1LB2LB1LA") c0.
Proof. solve_cert (NG 0 10000 10000 4 8 0 0 false). Time Qed.

Lemma nonhalt419: ~halts (TM_from_str "1RB2RA1LB1RA2RB_2LA4LB3LA0RA---") c0.
Proof. solve_cert (NG 0 10000 10000 4 8 0 0 false). Time Qed.

Lemma nonhalt420: ~halts (TM_from_str "1RB3LA1LA2RB3RB_2LB2RA0RA4RB---") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 12 3200 0 11 1 0). Time Qed.

Lemma nonhalt421: ~halts (TM_from_str "1RB2LA0RB1LB3LB_1LA3RA1RA4RA---") c0.
Proof. solve_cert (NG 0 10000 10000 1 4 4 0 true). Time Qed.

Lemma nonhalt422: ~halts (TM_from_str "1RB2RB---1LB3LB_1LA3RB4LB2RA0LB") c0.
Proof. solve_cert (NG 0 10000 10000 1 12 0 0 true). Time Qed.

Lemma nonhalt423: ~halts (TM_from_str "1RB2RB3RB2LA1LB_0LA---4LA4RA3RA") c0.
Proof. solve_cert (NG 0 10000 10000 1 12 0 0 true). Time Qed.

Lemma nonhalt424: ~halts (TM_from_str "1RB4LA3LA1LA0RA_2LB3RA---1RA2RB") c0.
Proof. solve_cert (NG 0 10000 10000 3 0 4 0 true). Time Qed.

Lemma nonhalt425: ~halts (TM_from_str "1RB4RB3LA1RB1LA_2LB2RA4LB2RB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt426: ~halts (TM_from_str "1RB1LA3LA4RB1RB_2LB2RA1LB2RB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt427: ~halts (TM_from_str "1RB1LA3LA0RB1LA_2LB2RA4LB2RB---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt428: ~halts (TM_from_str "1RB0LB---4RA3RA_2LA4LA3LB1LA1RA") c0.
Proof. solve_cert (NG 0 10000 10000 2 32 0 0 false). Time Qed.

Lemma nonhalt429: ~halts (TM_from_str "1RB3LA4LB2RB1RB_2LA1RB---4RA1LA") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 8 3200 2 4 4 0). Time Qed.

Lemma nonhalt430: ~halts (TM_from_str "1RB2LB---3LA0LB_2LA3RA3LB4RB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 14 3200 1 14 1 0). Time Qed.

Lemma nonhalt431: ~halts (TM_from_str "1RB3RB---4LB2RB_1LB2LA0RA4LB3RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt432: ~halts (TM_from_str "1RB3LA4LB2RB0RA_2LA4RA1LA1RB---") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 2 3200 0 2 1 0). Time Qed.

Lemma nonhalt433: ~halts (TM_from_str "1RB1LA4LB0RB---_2LA3LB0RA1RA1LB") c0.
Proof. solve_cert (NG 0 10000 10000 2 8 2 0 true). Time Qed.

Lemma nonhalt434: ~halts (TM_from_str "1RB2RB0LA1LA2LB_2LA3RA3LB4RA---") c0.
Proof. solve_cert (NG 0 10000 10000 2 12 2 0 true). Time Qed.

Lemma nonhalt435: ~halts (TM_from_str "1RB3LB0LA4RA3LA_2LA2RA3RB0RA---") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 6 4 0). Time Qed.

Lemma nonhalt436: ~halts (TM_from_str "1RB0RB3RA2LB---_2LA4RB3RB0LA0RA") c0.
Proof. solve_cert (NG 0 10000 10000 7 6 4 0 true). Time Qed.

Lemma nonhalt437: ~halts (TM_from_str "1RB2RA3LA0RB2RA_2LA---4LA2RB4LB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 9 3200 0 2 1 0). Time Qed.

Lemma nonhalt438: ~halts (TM_from_str "1RB3RA4LA4LA0RB_2LA1LB1LA---2RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 9 3200 0 2 1 0). Time Qed.

Lemma nonhalt439: ~halts (TM_from_str "1RB2RA3LA0RB2RA_2LA---4LA2RB1LB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 9 3200 0 2 1 0). Time Qed.

Lemma nonhalt440: ~halts (TM_from_str "1RB3LA3RB0LA1RA_2LA4RA0RA4LB---") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt441: ~halts (TM_from_str "1RB1LA4RA2RB0LB_2LA3RB1LA0RA---") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt442: ~halts (TM_from_str "1RB2LB4LB0LA3LB_2LA---3RA3RB0RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt443: ~halts (TM_from_str "1RB2RB3LA0LB---_2LA4LB2RB1LA0RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt444: ~halts (TM_from_str "1RB4RB3LA1RB2LA_1LB2LA2RB4RA---") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt445: ~halts (TM_from_str "1RB3LB---3LA0LB_2LA4RA1RA0RB3RA") c0.
Proof. solve_cert (NG 0 10000 10000 3 32 0 0 false). Time Qed.

Lemma nonhalt446: ~halts (TM_from_str "1RB3LB---4LA0RB_2LA4LA0RA2LA3RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 1 3200 2 3 3 0). Time Qed.

Lemma nonhalt447: ~halts (TM_from_str "1RB3RA4LA2RA3RB_2LA---3LA3LB2RB") c0.
Proof. solve_cert (RWL_mod 1001 10000 10000 2 3200 2 4 4 0). Time Qed.

Lemma nonhalt448: ~halts (TM_from_str "1RB3LB4RA---2LB_2LA0RA4RB0LA0LA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 4 3200 0 3 1 0). Time Qed.

Lemma nonhalt449: ~halts (TM_from_str "1RB3LA---4LB0LB_1LB2LA1RA4RB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 6 3200 1 3 0 0). Time Qed.

Lemma nonhalt450: ~halts (TM_from_str "1RB3RA4LB---2RB_2LA2LB0RB0LB3RA") c0.
Proof. solve_cert (CPS_LRU 1001 10000 10000 17 3200 0 4 0 0). Time Qed.

Lemma nonhalt451: ~halts (TM_from_str "1RB3RA4LA2RB---_2LB3RB0RB2RA0LA") c0.
Proof. solve_cert (RWL_mod 1001 30000 30000 8 3200 2 6 3 0). Time Qed.

Lemma nonhalt452: ~halts (TM_from_str "1RB2RA3LA4LA2RB_2LB1LA---1RB3RA") c0.
Proof. solve_cert (RWL_mod 1001 30000 30000 18 3200 2 3 2 0). Time Qed.

Lemma nonhalt453: ~halts (TM_from_str "1RB4LA3RB0LA---_2LB1RA3RA2LA0RB") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 15 3200 2 14 0 0). Time Qed.

Lemma nonhalt454: ~halts (TM_from_str "1RB3LA3LB0LA0RA_2LA---4LA4RA1RA") c0.
Proof. solve_cert (NG 0 30000 30000 7 12 10 0 true). Time Qed.

Lemma nonhalt455: ~halts (TM_from_str "1RB0LB4RB1RA0LA_2LA2RB3RB---1LA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt456: ~halts (TM_from_str "1RB2RB3RA---1LA_2LA4RB3LB1LB0RB") c0.
Proof. solve_cert (NG 0 30000 30000 3 6 2 0 true). Time Qed.

Lemma nonhalt457: ~halts (TM_from_str "1RB3RA4LA2RA0LA_2LA3LB1LA---2RB") c0.
Proof. solve_cert (NG 0 30000 30000 3 6 2 0 true). Time Qed.

Lemma nonhalt458: ~halts (TM_from_str "1RB3LA4RB---1LA_1LB2LA0RB4LB0RA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt459: ~halts (TM_from_str "1RB3LA1LA---2RB_2LA4LA0RA2LB0RB") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt460: ~halts (TM_from_str "1RB3LA1LA4LA1LB_2LA1RB---4RA3RB") c0.
Proof. solve_cert (NG 0 30000 30000 2 6 6 0 true). Time Qed.

Lemma nonhalt461: ~halts (TM_from_str "1RB2RB4RA---1LA_2LA4RB3LB1LB0RB") c0.
Proof. solve_cert (NG 0 30000 30000 2 12 0 0 true). Time Qed.

Lemma nonhalt462: ~halts (TM_from_str "1RB2RB0LA4RA0LB_1LA3RB4LA---1RB") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt463: ~halts (TM_from_str "1RB3RA4LA2RA0LA_2LA4LB1LA---2RB") c0.
Proof. solve_cert (NG 0 30000 30000 2 12 0 0 true). Time Qed.

Lemma nonhalt464: ~halts (TM_from_str "1RB3LA4RA0RB1RA_2LA2LB1LB2RA---") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 3 3200 0 2 0 0). Time Qed.

Lemma nonhalt465: ~halts (TM_from_str "1RB0LB4LB---3RA_2LA2LB3RA0RB1RA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt466: ~halts (TM_from_str "1RB3LB1RA0LA2LB_2LA4RA0RA---3LB") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 6 3200 1 2 0 0). Time Qed.

Lemma nonhalt467: ~halts (TM_from_str "1RB3RB---2LB3LB_2LA4RA4RB0LB0RB") c0.
Proof. solve_cert (NG 0 30000 30000 7 12 10 0 true). Time Qed.

Lemma nonhalt468: ~halts (TM_from_str "1RB3LA3RA0RB---_2LA4LA1RB0LB2RA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 3 3200 1 2 0 0). Time Qed.

Lemma nonhalt469: ~halts (TM_from_str "1RB3LA---0LB0LB_1LB2LA1RA4RB0RB") c0.
Proof. solve_cert (RWL_mod 1001 30000 30000 7 3200 2 1 2 0). Time Qed.

Lemma nonhalt470: ~halts (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4RB1LA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt471: ~halts (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LA1RB") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 2 3200 1 2 1 0). Time Qed.

Lemma nonhalt472: ~halts (TM_from_str "1RB2LA1LA0LB2RB_2LA4RA3RB2RB---") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 2 3200 2 2 2 0). Time Qed.

Lemma nonhalt473: ~halts (TM_from_str "1RB4RB1LA3RB3RA_1LB2RB3LA0LA---") c0.
Proof. solve_cert (RWL_mod 1001 30000 30000 3 3200 2 3 4 0). Time Qed.

Lemma nonhalt474: ~halts (TM_from_str "1RB2LB3RA4LB---_2LA2RB1LB0LA3LA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 24 3200 2 5 1 0). Time Qed.

Lemma nonhalt475: ~halts (TM_from_str "1RB3LA4RA1LB0LA_2LA2RA---4RA4LB") c0.
Proof. solve_cert (RWL_mod 1001 30000 30000 2 3200 2 3 3 0). Time Qed.

Lemma nonhalt476: ~halts (TM_from_str "1RB3LB3RA2RA---_2LA4RB2LB1LA0RA") c0.
Proof. solve_cert (CPS_LRU 1001 30000 30000 4 3200 0 2 1 0). Time Qed.

Lemma nonhalt477: ~halts (TM_from_str "1RB3LA1RB2LA1RA_1LB2LA3RA4RB---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 22 3200 2 6 12 0). Time Qed.

Lemma nonhalt478: ~halts (TM_from_str "1RB3LB4LB3RA---_2LA4RA4RA0LB3LB") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 1 3200 2 2 6 0). Time Qed.

Lemma nonhalt479: ~halts (TM_from_str "1RB2RA2LB2LB---_2LA4LA3RB0LA1RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 2 3200 1 3 0 0). Time Qed.

Lemma nonhalt480: ~halts (TM_from_str "1RB0LB4LA0RA---_2LA3RA3LB1LB3RB") c0.
Proof. solve_cert (NG 0 100000 100000 7 12 2 0 true). Time Qed.

Lemma nonhalt481: ~halts (TM_from_str "1RB2RA1LA4LA3LA_2LA3RB---0RB1RA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 3 3200 2 1 2 0). Time Qed.

Lemma nonhalt482: ~halts (TM_from_str "1RB2RB2LA4RB---_0LA3RA1LB1LA2RA") c0.
Proof. solve_cert (NG 0 100000 100000 7 12 2 0 true). Time Qed.

Lemma nonhalt483: ~halts (TM_from_str "1RB2LA4LA---2RA_1LA4RB3LB0LA1LB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 16 3200 2 14 0 0). Time Qed.

Lemma nonhalt484: ~halts (TM_from_str "1RB3RB---3RA1LA_2LA4RB3LB1LB3LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 16 3200 2 1 12 0). Time Qed.

Lemma nonhalt485: ~halts (TM_from_str "1RB3LA---4LA3RA_2LA4RB1RA1LB1RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt486: ~halts (TM_from_str "1RB3LA---1RA1LA_2LA4LB1RA4RB3RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt487: ~halts (TM_from_str "1RB3LA---1RA1LA_2LA4LB4RA4RB3RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 4 3200 1 2 0 0). Time Qed.

Lemma nonhalt488: ~halts (TM_from_str "1RB2RB1LA1LB0LB_2LA2RA3LA4RA---") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 20 3200 2 2 3 0). Time Qed.

Lemma nonhalt489: ~halts (TM_from_str "1RB0LB0RA---1RA_2LA0LB3RA4LA2RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 7 3200 1 2 0 0). Time Qed.

Lemma nonhalt490: ~halts (TM_from_str "1RB0LB0RA---1RA_2LA0LB3RA4LB2RB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 7 3200 1 2 0 0). Time Qed.

Lemma nonhalt491: ~halts (TM_from_str "1RB3LB0RA4RB1LA_2LA0LB0RA---2LB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 7 3200 1 2 0 0). Time Qed.

Lemma nonhalt492: ~halts (TM_from_str "1RB3LB0RA4RA1LA_2LA0LB0RA---2LB") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 7 3200 1 2 0 0). Time Qed.

Lemma nonhalt493: ~halts (TM_from_str "1RB3LA4LA1RA2RB_2LA---0LB4RA3LA") c0.
Proof. solve_cert (RWL_mod 1001 100000 100000 4 3200 2 4 6 0). Time Qed.

Lemma nonhalt494: ~halts (TM_from_str "1RB0RB1RA2LB---_2LA4RB3RB0LA1RA") c0.
Proof. solve_cert (CPS_LRU 1001 100000 100000 4 3200 1 2 1 0). Time Qed.

Lemma nonhalt495: ~halts (TM_from_str "1RB4RA3RA0LA1LA_1LB2LA3RB4LB---") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 1 3200 2 2 8 0). Time Qed.

Lemma nonhalt496: ~halts (TM_from_str "1RB3LA4LA0RB---_2LA2RA1RB0LB3RA") c0.
Proof. solve_cert (RWL_mod 1001 300000 300000 3 3200 2 2 3 0). Time Qed.

Lemma nonhalt497: ~halts (TM_from_str "1RB2RA1LA4LA3LA_2LA3RB---1RB1RA") c0.
Proof. solve_cert (CPS_LRU 1001 300000 300000 2 3200 2 4 0 0). Time Qed.

Lemma nonhalt498: ~halts (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LA2LB") c0.
Proof. solve_cert (CPS_LRU 0 800000 800000 2 3200 1 2 2 0). Time Qed.

Lemma nonhalt499: ~halts (TM_from_str "1RB3RA3LB0LA3RB_2LA3RB4RA1LA---") c0.
Proof. solve_cert (RWL_mod 1001 1000000 1000000 4 3200 2 12 6 0). Time Qed.

