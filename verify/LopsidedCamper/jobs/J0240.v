From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32985348833280 to 33122787786752 *)
Lemma J0240 : job_ok 137438953472 9889372836594 2 138544692116715 49526083119343 1 99526457205961.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 49526083119343 1 99526457205961))]. Qed.
