From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52913997086720 to 53051436040192 *)
Lemma J0385 : job_ok 137438953472 173290161130451 1 64822825678224 13463191896018 2 225268270259756.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13463191896018 2 225268270259756))]. Qed.
