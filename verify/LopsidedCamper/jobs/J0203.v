From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27900107554816 to 28037546508288 *)
Lemma J0203 : job_ok 137438953472 23564756705101 1 101985722644809 21374708265986 2 104794245886640.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21374708265986 2 104794245886640))]. Qed.
