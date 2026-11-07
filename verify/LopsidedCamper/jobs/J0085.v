From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11682311045120 to 11819749998592 *)
Lemma J0085 : job_ok 137438953472 19953744803293 1 32616656219132 29006413437003 1 24182463054403.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 29006413437003 1 24182463054403))]. Qed.
