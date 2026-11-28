From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2336462209024 to 2473901162496 *)
Lemma J0017 : job_ok 137438953472 5218702863760 2 5295376862494 3975268304025 1 7157287172457.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3975268304025 1 7157287172457))]. Qed.
