From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42193758715904 to 42331197669376 *)
Lemma J0307 : job_ok 137438953472 97352207913267 1 92519702492882 36353460226675 1 154136925848504.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 36353460226675 1 154136925848504))]. Qed.
