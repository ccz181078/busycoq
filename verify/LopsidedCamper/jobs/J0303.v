From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41644002902016 to 41781441855488 *)
Lemma J0303 : job_ok 137438953472 120754912456017 1 66643095866609 182694003042893 1 5322481007026.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 182694003042893 1 5322481007026))]. Qed.
