(* visits 0 to 200000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg000 : seg 200000000000 200000000000 2 9 3977785707 696022150165 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
