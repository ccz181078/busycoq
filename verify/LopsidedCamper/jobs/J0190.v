From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26113401159680 to 26250840113152 *)
Lemma J0190 : job_ok 137438953472 116205736298795 1 1304565559185 39741460473890 2 78387316580293.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 39741460473890 2 78387316580293))]. Qed.
