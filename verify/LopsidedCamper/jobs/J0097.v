From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13331578486784 to 13469017440256 *)
Lemma J0097 : job_ok 137438953472 30144873882035 1 29847229209711 2725728112141 1 57884849605936.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2725728112141 1 57884849605936))]. Qed.
