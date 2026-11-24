(* visits 400000000000 to 600000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg002 : seg 200000000000 200000000000 1183840927353 216158537422 728470578915 1371529232623 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
