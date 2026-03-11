From BusyCoq Require Import CTL25.

Ltac solve_cert ::= Nsolve_cert.

Lemma nonhalt1: ~halts (TM_from_str "1RB2LA0RB1LB0LB_1LA3RA1RA4RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 3000000 300000 2 3200 1 5 0 0). Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB2RB---0LB3LA_2LA2LB3RB4RB1LB") c0.
Proof. solve_cert (CPS_LRU_FAR 20000000 10000000 2 3200 5 3 0 0). Time Qed.

Lemma nonhalt3: ~halts (TM_from_str "1LB3RA1LA4RA2LA_2RA---1RA0LA3LB") c0.
Proof. solve_cert (CPS_LRU_FAR 200000000 100000000 2 3200 5 5 0 0). Time Qed.


