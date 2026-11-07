From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25975962206208 to 26113401159680 *)
Lemma J0189 : job_ok 137438953472 36494709863109 1 80397116538268 116205736298795 1 1304565559185.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 116205736298795 1 1304565559185))]. Qed.
