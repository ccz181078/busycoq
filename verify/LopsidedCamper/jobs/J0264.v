From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36283883716608 to 36421322670080 *)
Lemma J0264 : job_ok 137438953472 37260078832370 2 126017392708901 87985238511051 1 75910708462499.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 87985238511051 1 75910708462499))]. Qed.
