From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58823872086016 to 58961311039488 *)
Lemma J0428 : job_ok 137438953472 26648779044235 1 238058643839034 215476180272794 2 49849718174389.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 215476180272794 2 49849718174389))]. Qed.
