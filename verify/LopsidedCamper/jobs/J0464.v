From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63771674411008 to 63909113364480 *)
Lemma J0464 : job_ok 137438953472 138275282678977 1 148697251046682 244433664486863 1 43157343689755.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 244433664486863 1 43157343689755))]. Qed.
