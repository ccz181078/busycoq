From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31198642438144 to 31336081391616 *)
Lemma J0227 : job_ok 137438953472 16297459075495 1 124096427697025 37952658836885 1 103059702495456.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 37952658836885 1 103059702495456))]. Qed.
