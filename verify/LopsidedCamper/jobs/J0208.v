From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28587302322176 to 28724741275648 *)
Lemma J0208 : job_ok 137438953472 95467995741170 2 33174859487864 4090332330277 1 125170997956810.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4090332330277 1 125170997956810))]. Qed.
