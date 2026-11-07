From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33535104647168 to 33672543600640 *)
Lemma J0244 : job_ok 137438953472 95317609668159 1 55590355614261 119366428565658 2 32160012269054.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 119366428565658 2 32160012269054))]. Qed.
