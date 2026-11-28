(* visits 600000000000 to 800000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg003 : seg 200000000000 200000000000 728470578915 1371529232623 943261329281 1856738326878 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
