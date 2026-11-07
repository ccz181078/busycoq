From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65695819759616 to 65833258713088 *)
Lemma J0478 : job_ok 137438953472 114277804874655 1 181353384107575 151297154145355 1 144952510713144.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 151297154145355 1 144952510713144))]. Qed.
