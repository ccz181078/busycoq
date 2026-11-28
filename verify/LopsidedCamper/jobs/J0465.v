From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63909113364480 to 64046552317952 *)
Lemma J0465 : job_ok 137438953472 244433664486863 1 43157343689755 24917390114957 1 263292093759032.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24917390114957 1 263292093759032))]. Qed.
