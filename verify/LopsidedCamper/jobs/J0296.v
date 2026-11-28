From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40681930227712 to 40819369181184 *)
Lemma J0296 : job_ok 137438953472 7890773797424 2 175177907114463 98255925228827 1 85431230782347.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98255925228827 1 85431230782347))]. Qed.
