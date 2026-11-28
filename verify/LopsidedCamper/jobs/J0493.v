From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67757404061696 to 67894843015168 *)
Lemma J0493 : job_ok 137438953472 129037073555984 2 175871245835232 51846982604272 2 253679811654309.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 51846982604272 2 253679811654309))]. Qed.
