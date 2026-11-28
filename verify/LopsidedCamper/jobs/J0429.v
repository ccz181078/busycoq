From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 58961311039488 to 59098749992960 *)
Lemma J0429 : job_ok 137438953472 215476180272794 2 49849718174389 84176725757945 1 181767647455735.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 84176725757945 1 181767647455735))]. Qed.
