From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30511447670784 to 30648886624256 *)
Lemma J0222 : job_ok 137438953472 40226454591073 1 97075055944093 66702912986301 1 71217072834522.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 66702912986301 1 71217072834522))]. Qed.
