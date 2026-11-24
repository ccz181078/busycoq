(* visits 79800000000000 to 79859656218974 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg399 : seg_halt 59656218974 59656218974 208496432744458 70803563135337 279508792558980 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
