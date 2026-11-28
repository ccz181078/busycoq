From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48378511622144 to 48515950575616 *)
Lemma J0352 : job_ok 137438953472 81788663948429 1 135914637311114 199007476398075 1 19314300171110.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 199007476398075 1 19314300171110))]. Qed.
