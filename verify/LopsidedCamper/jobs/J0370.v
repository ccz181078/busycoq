From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50852412784640 to 50989851738112 *)
Lemma J0370 : job_ok 137438953472 160188179150769 1 68647679811294 38409788401803 1 191044545628764.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 38409788401803 1 191044545628764))]. Qed.
