From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43430709297152 to 43568148250624 *)
Lemma J0316 : job_ok 137438953472 40276669496607 1 155161518371530 122892403444579 1 73164260182788.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 122892403444579 1 73164260182788))]. Qed.
