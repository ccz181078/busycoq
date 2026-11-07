From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30374008717312 to 30511447670784 *)
Lemma J0221 : job_ok 137438953472 90749045043885 1 45933990097970 40226454591073 1 97075055944093.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 40226454591073 1 97075055944093))]. Qed.
