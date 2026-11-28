From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29137058136064 to 29274497089536 *)
Lemma J0212 : job_ok 137438953472 102974424512053 1 28142330850532 98079662006937 1 33655568347535.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98079662006937 1 33655568347535))]. Qed.
