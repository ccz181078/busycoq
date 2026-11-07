From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35459249995776 to 35596688949248 *)
Lemma J0258 : job_ok 137438953472 123532649199519 1 36033970761706 93863146900552 2 66321948867346.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 93863146900552 2 66321948867346))]. Qed.
