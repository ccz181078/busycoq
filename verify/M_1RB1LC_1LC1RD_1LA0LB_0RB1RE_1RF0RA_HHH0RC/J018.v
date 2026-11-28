(* visits 3600000000000 to 3800000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg018 : seg 200000000000 200000000000 8702439615444 3897559574215 4178937371332 9121062100017 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
