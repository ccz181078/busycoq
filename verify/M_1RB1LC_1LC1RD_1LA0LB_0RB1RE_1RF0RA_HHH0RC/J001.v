(* visits 200000000000 to 400000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg001 : seg 200000000000 200000000000 3977785707 696022150165 1183840927353 216158537422 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
