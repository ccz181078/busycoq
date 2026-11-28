From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54013508714496 to 54150947667968 *)
Lemma J0393 : job_ok 137438953472 228931290095258 2 14129499258536 28558609441699 1 215120655100246.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 28558609441699 1 215120655100246))]. Qed.
