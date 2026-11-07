From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42331197669376 to 42468636622848 *)
Lemma J0308 : job_ok 137438953472 36353460226675 1 154136925848504 15594175647650 2 175514685631553.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 15594175647650 2 175514685631553))]. Qed.
