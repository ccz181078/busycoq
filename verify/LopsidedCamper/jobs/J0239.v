From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32847909879808 to 32985348833280 *)
Lemma J0239 : job_ok 137438953472 112917970633521 1 34897618943057 9889372836594 2 138544692116715.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9889372836594 2 138544692116715))]. Qed.
