From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67894843015168 to 68032281968640 *)
Lemma J0494 : job_ok 137438953472 51846982604272 2 253679811654309 34409389680667 1 271735879293740.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34409389680667 1 271735879293740))]. Qed.
