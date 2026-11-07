From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11544872091648 to 11682311045120 *)
Lemma J0084 : job_ok 137438953472 13106861129559 1 38845065029575 19953744803293 1 32616656219132.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 19953744803293 1 32616656219132))]. Qed.
