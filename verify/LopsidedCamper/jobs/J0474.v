From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65146063945728 to 65283502899200 *)
Lemma J0474 : job_ok 137438953472 185827561507613 1 107329725415394 216342244821529 1 77433518192863.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 216342244821529 1 77433518192863))]. Qed.
