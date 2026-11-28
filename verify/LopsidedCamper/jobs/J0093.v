From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12781822672896 to 12919261626368 *)
Lemma J0093 : job_ok 137438953472 6943366945354 2 50574834910937 17304138916813 1 40832538753650.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 17304138916813 1 40832538753650))]. Qed.
