From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8246337208320 to 8383776161792 *)
Lemma J0060 : job_ok 137438953472 6460627542426 2 30647888168926 14340718471747 1 23386272617740.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 14340718471747 1 23386272617740))]. Qed.
