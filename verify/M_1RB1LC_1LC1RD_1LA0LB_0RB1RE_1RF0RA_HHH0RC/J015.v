(* visits 3000000000000 to 3200000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg015 : seg 200000000000 200000000000 6583418669566 3916580488195 6472745151579 4727253848047 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
