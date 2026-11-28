From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40819369181184 to 40956808134656 *)
Lemma J0297 : job_ok 137438953472 98255925228827 1 85431230782347 8606040832418 2 175699590541902.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8606040832418 2 175699590541902))]. Qed.
