From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67619965108224 to 67757404061696 *)
Lemma J0492 : job_ok 137438953472 240691931244781 1 63597913368406 129037073555984 2 175871245835232.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 129037073555984 2 175871245835232))]. Qed.
