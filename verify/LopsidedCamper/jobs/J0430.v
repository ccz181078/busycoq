From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59098749992960 to 59236188946432 *)
Lemma J0430 : job_ok 137438953472 84176725757945 1 181767647455735 73738938664658 2 192823909522479.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 73738938664658 2 192823909522479))]. Qed.
