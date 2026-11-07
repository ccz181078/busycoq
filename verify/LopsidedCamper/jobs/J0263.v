From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36146444763136 to 36283883716608 *)
Lemma J0263 : job_ok 137438953472 47045335765813 1 115613660644360 37260078832370 2 126017392708901.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 37260078832370 2 126017392708901))]. Qed.
