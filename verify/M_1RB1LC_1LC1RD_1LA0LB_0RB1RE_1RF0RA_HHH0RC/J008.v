(* visits 1600000000000 to 1800000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg008 : seg 200000000000 200000000000 4866391856084 733607754173 3633700803637 2666299348738 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
