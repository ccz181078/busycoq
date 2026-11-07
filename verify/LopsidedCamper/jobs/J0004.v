From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 549755813888 to 687194767360 *)
Lemma J0004 : job_ok 137438953472 458222115325 1 2015678747475 1453896559715 1 1638479380020.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1453896559715 1 1638479380020))]. Qed.
