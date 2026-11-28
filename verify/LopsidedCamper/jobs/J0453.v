From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62259845922816 to 62397284876288 *)
Lemma J0453 : job_ok 137438953472 256002824011346 2 24166480990729 273840380199469 1 6947400606350.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 273840380199469 1 6947400606350))]. Qed.
