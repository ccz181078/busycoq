From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70918499991552 to 71055938945024 *)
Lemma J0516 : job_ok 137438953472 123204082657195 1 195929167737289 286885484609813 1 32866240392269.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 286885484609813 1 32866240392269))]. Qed.
