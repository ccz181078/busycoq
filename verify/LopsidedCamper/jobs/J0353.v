From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48515950575616 to 48653389529088 *)
Lemma J0353 : job_ok 137438953472 199007476398075 1 19314300171110 160836789009839 1 58103462760537.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 160836789009839 1 58103462760537))]. Qed.
