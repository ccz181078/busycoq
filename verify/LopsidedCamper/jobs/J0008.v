From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1099511627776 to 1236950581248 *)
Lemma J0008 : job_ok 137438953472 1235590089559 1 3712211384197 217528674025 1 5348747600873.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 217528674025 1 5348747600873))]. Qed.
