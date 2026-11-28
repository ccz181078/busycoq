From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70781061038080 to 70918499991552 *)
Lemma J0515 : job_ok 137438953472 164139818268527 1 154374956809630 123204082657195 1 195929167737289.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 123204082657195 1 195929167737289))]. Qed.
