(* visits 3800000000000 to 4000000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg019 : seg 200000000000 200000000000 4178937371332 9121062100017 7354046713435 6645952891241 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
