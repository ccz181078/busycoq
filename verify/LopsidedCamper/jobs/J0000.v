From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 0 to 137438953472 *)
Lemma J0000 : job_ok 137438953472 0 1 0 349018790754 2 269456661313.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 349018790754 2 269456661313))]. Qed.
