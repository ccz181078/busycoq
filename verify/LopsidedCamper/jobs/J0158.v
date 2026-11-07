From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21715354648576 to 21852793602048 *)
Lemma J0158 : job_ok 137438953472 88911918486067 1 8807173424700 56615325799970 2 41722241429097.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 56615325799970 2 41722241429097))]. Qed.
