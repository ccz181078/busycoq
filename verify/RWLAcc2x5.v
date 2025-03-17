From BusyCoq Require Import RWLAcc25.

Ltac solve_nonhalt bsz bmaxT mnc T :=
  eapply (decide_nonhalt_spec _ bsz bmaxT true mnc T);
  native_cast_no_check (eq_refl true). 

Lemma nonhalt1: ~halts (TM_from_str "1RB2RB1LA4RA0LB_2LA2RA3LA1LB---") c0.
Proof. solve_nonhalt 7 3200 0%N (10^8)%N. Time Qed.

