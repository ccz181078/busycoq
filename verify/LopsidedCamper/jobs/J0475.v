From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65283502899200 to 65420941852672 *)
Lemma J0475 : job_ok 137438953472 216342244821529 1 77433518192863 215851358422379 1 78542879266848.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 215851358422379 1 78542879266848))]. Qed.
