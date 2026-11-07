From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43293270343680 to 43430709297152 *)
Lemma J0315 : job_ok 137438953472 41055954775469 1 153763758086858 40276669496607 1 155161518371530.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 40276669496607 1 155161518371530))]. Qed.
