From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68719476736000 to 68856915689472 *)
Lemma J0500 : job_ok 137438953472 198301674575243 1 110935971649129 12877078032451 1 296979043261204.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 12877078032451 1 296979043261204))]. Qed.
