From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28449863368704 to 28587302322176 *)
Lemma J0207 : job_ok 137438953472 87033199528543 1 40991180437416 95467995741170 2 33174859487864.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 95467995741170 2 33174859487864))]. Qed.
