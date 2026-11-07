From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60610578481152 to 60748017434624 *)
Lemma J0441 : job_ok 137438953472 78026980271763 1 194720620089058 170527630943997 1 102838444442138.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 170527630943997 1 102838444442138))]. Qed.
