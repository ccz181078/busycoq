From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5222680231936 to 5360119185408 *)
Lemma J0038 : job_ok 137438953472 4043665158979 1 19458394969748 13669813533650 2 10450721723678.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13669813533650 2 10450721723678))]. Qed.
