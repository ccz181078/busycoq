From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25838523252736 to 25975962206208 *)
Lemma J0188 : job_ok 137438953472 46051602346737 1 70221748786515 36494709863109 1 80397116538268.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 36494709863109 1 80397116538268))]. Qed.
