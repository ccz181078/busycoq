From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 274877906944 to 412316860416 *)
Lemma J0002 : job_ok 137438953472 828590691805 1 408359980468 1826726716919 1 28698735924.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1826726716919 1 28698735924))]. Qed.
