From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51127290691584 to 51264729645056 *)
Lemma J0372 : job_ok 137438953472 30731438613135 1 199341371358025 126813681259994 2 103877604112002.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 126813681259994 2 103877604112002))]. Qed.
