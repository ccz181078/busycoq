From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40269613367296 to 40407052320768 *)
Lemma J0293 : job_ok 137438953472 67399341563881 1 113813914178297 117232136866178 2 64599594192155.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 117232136866178 2 64599594192155))]. Qed.
