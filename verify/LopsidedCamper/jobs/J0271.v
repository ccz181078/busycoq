From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37245956390912 to 37383395344384 *)
Lemma J0271 : job_ok 137438953472 124506452275066 2 43100346990094 77610000526501 1 90615274162731.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 77610000526501 1 90615274162731))]. Qed.
