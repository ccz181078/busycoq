From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25701084299264 to 25838523252736 *)
Lemma J0187 : job_ok 137438953472 101383842974327 1 14271032686156 46051602346737 1 70221748786515.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 46051602346737 1 70221748786515))]. Qed.
