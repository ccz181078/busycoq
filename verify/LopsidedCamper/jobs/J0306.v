From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42056319762432 to 42193758715904 *)
Lemma J0306 : job_ok 137438953472 103020149669810 2 86233285669932 97352207913267 1 92519702492882.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 97352207913267 1 92519702492882))]. Qed.
