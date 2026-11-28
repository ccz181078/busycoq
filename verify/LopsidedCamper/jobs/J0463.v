From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63634235457536 to 63771674411008 *)
Lemma J0463 : job_ok 137438953472 190739342413458 2 95614716055943 138275282678977 1 148697251046682.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 138275282678977 1 148697251046682))]. Qed.
