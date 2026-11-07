From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35321811042304 to 35459249995776 *)
Lemma J0257 : job_ok 137438953472 136007475807954 2 22940669997466 123532649199519 1 36033970761706.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 123532649199519 1 36033970761706))]. Qed.
