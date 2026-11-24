(* visits 3200000000000 to 3400000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg016 : seg 200000000000 200000000000 6472745151579 4727253848047 2422472331946 9477526717989 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
