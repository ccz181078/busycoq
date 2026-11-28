From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6734508720128 to 6871947673600 *)
Lemma J0049 : job_ok 137438953472 18977088666595 1 11328197267533 29519520486489 1 1404240648126.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 29519520486489 1 1404240648126))]. Qed.
