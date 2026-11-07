From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53601191854080 to 53738630807552 *)
Lemma J0390 : job_ok 137438953472 137899208611521 1 103306154279007 78991222343165 1 162832615569314.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 78991222343165 1 162832615569314))]. Qed.
