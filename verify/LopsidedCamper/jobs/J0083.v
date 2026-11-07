From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11407433138176 to 11544872091648 *)
Lemma J0083 : job_ok 137438953472 8789443491657 1 42544007590259 13106861129559 1 38845065029575.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13106861129559 1 38845065029575))]. Qed.
