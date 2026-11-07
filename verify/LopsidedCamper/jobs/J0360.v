From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49478023249920 to 49615462203392 *)
Lemma J0360 : job_ok 137438953472 106249268933205 1 116401835585312 153287018754627 1 69982561075156.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 153287018754627 1 69982561075156))]. Qed.
