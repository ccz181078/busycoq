From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54150947667968 to 54288386621440 *)
Lemma J0394 : job_ok 137438953472 28558609441699 1 215120655100246 23808147054421 1 220489593414711.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 23808147054421 1 220489593414711))]. Qed.
