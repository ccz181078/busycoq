From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58686433132544 to 58823872086016 *)
Lemma J0427 : job_ok 137438953472 158017288017306 2 106071659138831 26648779044235 1 238058643839034.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 26648779044235 1 238058643839034))]. Qed.
