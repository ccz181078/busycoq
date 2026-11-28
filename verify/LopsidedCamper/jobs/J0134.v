From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18416819765248 to 18554258718720 *)
Lemma J0134 : job_ok 137438953472 65709605638955 1 17166084748051 4352944840290 2 79141220709622.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4352944840290 2 79141220709622))]. Qed.
