(* visits 2600000000000 to 2800000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg013 : seg 200000000000 200000000000 3899885666285 5200113996363 1911872843568 7888126836829 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
