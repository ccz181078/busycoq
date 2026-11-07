From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39170101739520 to 39307540692992 *)
Lemma J0285 : job_ok 137438953472 136619650022303 1 39645803462605 67505018949583 1 109378910268130.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 67505018949583 1 109378910268130))]. Qed.
