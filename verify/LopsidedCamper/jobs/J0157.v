From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21577915695104 to 21715354648576 *)
Lemma J0157 : job_ok 137438953472 24778159963346 2 72322456008737 88911918486067 1 8807173424700.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 88911918486067 1 8807173424700))]. Qed.
