From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36833639530496 to 36971078483968 *)
Lemma J0268 : job_ok 137438953472 41556192949218 2 124195180115994 122183004507208 2 44186844062660.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 122183004507208 2 44186844062660))]. Qed.
