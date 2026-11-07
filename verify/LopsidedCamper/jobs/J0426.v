From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58548994179072 to 58686433132544 *)
Lemma J0426 : job_ok 137438953472 136773916463939 1 126696555808070 158017288017306 2 106071659138831.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 158017288017306 2 106071659138831))]. Qed.
