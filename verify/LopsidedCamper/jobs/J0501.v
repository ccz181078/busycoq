From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68856915689472 to 68994354642944 *)
Lemma J0501 : job_ok 137438953472 12877078032451 1 296979043261204 275817107242930 2 34657489797062.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 275817107242930 2 34657489797062))]. Qed.
