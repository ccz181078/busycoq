(* visits 1200000000000 to 1400000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg006 : seg 200000000000 200000000000 604590894820 3595408878841 4357263535201 542736085389 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
