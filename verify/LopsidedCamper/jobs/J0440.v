From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60473139527680 to 60610578481152 *)
Lemma J0440 : job_ok 137438953472 142909450460015 1 129219674874381 78026980271763 1 194720620089058.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 78026980271763 1 194720620089058))]. Qed.
