From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1374389534720 to 1511828488192 *)
Lemma J0010 : job_ok 137438953472 5738899819578 2 445852360520 3370487406417 1 3432740026240.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3370487406417 1 3432740026240))]. Qed.
