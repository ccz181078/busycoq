(* visits 1400000000000 to 1600000000000 *)
From Coq Require Import Uint63 PArith.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Check.
Lemma seg007 : seg 200000000000 200000000000 4357263535201 542736085389 4866391856084 733607754173 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
