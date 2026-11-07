From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36696200577024 to 36833639530496 *)
Lemma J0267 : job_ok 137438953472 38769273221789 1 126363624098014 41556192949218 2 124195180115994.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 41556192949218 2 124195180115994))]. Qed.
