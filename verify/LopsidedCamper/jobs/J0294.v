From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40407052320768 to 40544491274240 *)
Lemma J0294 : job_ok 137438953472 117232136866178 2 64599594192155 11442890462685 1 171007315688714.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11442890462685 1 171007315688714))]. Qed.
