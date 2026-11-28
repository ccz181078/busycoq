From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6871947673600 to 7009386627072 *)
Lemma J0050 : job_ok 137438953472 29519520486489 1 1404240648126 17812492468569 1 13729744438269.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 17812492468569 1 13729744438269))]. Qed.
