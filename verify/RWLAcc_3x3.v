From BusyCoq Require Import RWLAcc33.

Ltac solve_nonhalt' bsz bmaxT mnc T :=
  eapply (decide_nonhalt_spec _ bsz bmaxT true mnc T);
  native_cast_no_check (eq_refl true). 

Ltac solve_nonhalt bsz := solve_nonhalt' bsz 3200 N0 (10^8)%N.

Lemma nonhalt1: ~halts (TM_from_str "1RB0RB1LB_1LA2RB2RC_---2LA0RA") c0.
Proof. solve_nonhalt 4. Time Qed.

Lemma nonhalt2: ~halts (TM_from_str "1RB2LA2LC_1LA0LA1RA_---2RB0LB") c0.
Proof. solve_nonhalt 4. Time Qed.


