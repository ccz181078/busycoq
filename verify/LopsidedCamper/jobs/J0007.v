From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 962072674304 to 1099511627776 *)
Lemma J0007 : job_ok 137438953472 1418253431287 1 2911073130399 1235590089559 1 3712211384197.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1235590089559 1 3712211384197))]. Qed.
