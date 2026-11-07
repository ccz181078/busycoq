From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70231305224192 to 70368744177664 *)
Lemma J0511 : job_ok 137438953472 174759916054617 1 141280958646527 153568665395655 1 163090684896888.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 153568665395655 1 163090684896888))]. Qed.
