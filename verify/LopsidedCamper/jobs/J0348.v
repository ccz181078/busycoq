From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47828755808256 to 47966194761728 *)
Lemma J0348 : job_ok 137438953472 213892924143625 1 1336476221698 187920221807775 1 27927653670627.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 187920221807775 1 27927653670627))]. Qed.
