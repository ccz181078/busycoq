From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42468636622848 to 42606075576320 *)
Lemma J0309 : job_ok 137438953472 15594175647650 2 175514685631553 184499372734631 1 7227963986653.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 184499372734631 1 7227963986653))]. Qed.
