From BusyCoq Require Import CTL25.

Ltac solve_cert ::= Nsolve_cert.

Lemma nonhalt1: ~halts (TM_from_str "1RB2LA0RB1LB0LB_1LA3RA1RA4RA---") c0.
Proof. solve_cert (CPS_LRU_FAR 3000000 300000 2 3200 1 5 0 0). Time Qed.


