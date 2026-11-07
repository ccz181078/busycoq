From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9895604649984 to 10033043603456 *)
Lemma J0072 : job_ok 137438953472 2947032382169 1 41583189320779 35349648565725 1 9799048442506.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 35349648565725 1 9799048442506))]. Qed.
