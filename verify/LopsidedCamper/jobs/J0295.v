From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40544491274240 to 40681930227712 *)
Lemma J0295 : job_ok 137438953472 11442890462685 1 171007315688714 7890773797424 2 175177907114463.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 7890773797424 2 175177907114463))]. Qed.
