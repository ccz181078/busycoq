(* visits 1000000000000 to 1200000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg005 : seg 200000000000 200000000000 2371048047986 1128951743257 604590894820 3595408878841 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
