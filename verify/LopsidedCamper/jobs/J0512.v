From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70368744177664 to 70506183131136 *)
Lemma J0512 : job_ok 137438953472 153568665395655 1 163090684896888 31825887802191 1 285451937518684.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31825887802191 1 285451937518684))]. Qed.
