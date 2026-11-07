From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27762668601344 to 27900107554816 *)
Lemma J0202 : job_ok 137438953472 83790785483707 1 41141218795566 23564756705101 1 101985722644809.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 23564756705101 1 101985722644809))]. Qed.
