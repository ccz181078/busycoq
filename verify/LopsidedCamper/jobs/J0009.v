From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1236950581248 to 1374389534720 *)
Lemma J0009 : job_ok 137438953472 217528674025 1 5348747600873 5738899819578 2 445852360520.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5738899819578 2 445852360520))]. Qed.
