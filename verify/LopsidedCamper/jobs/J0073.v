From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10033043603456 to 10170482556928 *)
Lemma J0073 : job_ok 137438953472 35349648565725 1 9799048442506 21409082885818 2 24358089784612.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21409082885818 2 24358089784612))]. Qed.
