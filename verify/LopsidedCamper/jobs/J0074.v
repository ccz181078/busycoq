From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10170482556928 to 10307921510400 *)
Lemma J0074 : job_ok 137438953472 21409082885818 2 24358089784612 16286286016529 1 30099362599545.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16286286016529 1 30099362599545))]. Qed.
