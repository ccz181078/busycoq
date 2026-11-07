From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 412316860416 to 549755813888 *)
Lemma J0003 : job_ok 137438953472 1826726716919 1 28698735924 458222115325 1 2015678747475.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 458222115325 1 2015678747475))]. Qed.
