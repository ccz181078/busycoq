From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47691316854784 to 47828755808256 *)
Lemma J0347 : job_ok 137438953472 63378695616863 1 151232229657581 213892924143625 1 1336476221698.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 213892924143625 1 1336476221698))]. Qed.
