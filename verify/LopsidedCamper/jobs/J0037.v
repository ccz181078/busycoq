From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5085241278464 to 5222680231936 *)
Lemma J0037 : job_ok 137438953472 10092748123427 1 12790836975444 4043665158979 1 19458394969748.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4043665158979 1 19458394969748))]. Qed.
