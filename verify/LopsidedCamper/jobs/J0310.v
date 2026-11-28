From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42606075576320 to 42743514529792 *)
Lemma J0310 : job_ok 137438953472 184499372734631 1 7227963986653 113555107867173 1 78790703857544.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 113555107867173 1 78790703857544))]. Qed.
