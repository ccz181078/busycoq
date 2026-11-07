From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15530601742336 to 15668040695808 *)
Lemma J0113 : job_ok 137438953472 53451730909107 1 16435976911448 34819151157433 1 35687031753569.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34819151157433 1 35687031753569))]. Qed.
