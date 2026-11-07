From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15668040695808 to 15805479649280 *)
Lemma J0114 : job_ok 137438953472 34819151157433 1 35687031753569 57419390152783 1 13705267844927.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 57419390152783 1 13705267844927))]. Qed.
