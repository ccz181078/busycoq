From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51264729645056 to 51402168598528 *)
Lemma J0373 : job_ok 137438953472 126813681259994 2 103877604112002 696308921219 1 230613451434016.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 696308921219 1 230613451434016))]. Qed.
