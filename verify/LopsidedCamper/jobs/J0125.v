From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17179869184000 to 17317308137472 *)
Lemma J0125 : job_ok 137438953472 55364228606087 1 21945184711438 26913461999312 2 51014426362683.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 26913461999312 2 51014426362683))]. Qed.
