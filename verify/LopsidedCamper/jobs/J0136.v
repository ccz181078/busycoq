From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18691697672192 to 18829136625664 *)
Lemma J0136 : job_ok 137438953472 72802621540043 1 11310018719530 48298266485049 1 36432849173345.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 48298266485049 1 36432849173345))]. Qed.
