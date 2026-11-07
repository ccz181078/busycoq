From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5634997092352 to 5772436045824 *)
Lemma J0041 : job_ok 137438953472 17518833947811 1 7838650827635 23263147479449 1 2712813072687.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 23263147479449 1 2712813072687))]. Qed.
