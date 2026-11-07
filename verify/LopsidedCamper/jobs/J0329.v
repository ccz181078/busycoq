From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45217415692288 to 45354854645760 *)
Lemma J0329 : job_ok 137438953472 63015185410267 1 140463182824222 196357903699789 1 7738939829569.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 196357903699789 1 7738939829569))]. Qed.
