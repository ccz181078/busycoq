From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 17042430230528 to 17179869184000 *)
Lemma J0124 : job_ok 137438953472 52805038843341 1 23885898724606 55364228606087 1 21945184711438.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 55364228606087 1 21945184711438))]. Qed.
