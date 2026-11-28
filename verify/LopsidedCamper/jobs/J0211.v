From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28999619182592 to 29137058136064 *)
Lemma J0211 : job_ok 137438953472 129080930782512 2 1417349083370 102974424512053 1 28142330850532.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 102974424512053 1 28142330850532))]. Qed.
