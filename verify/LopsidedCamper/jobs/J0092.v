From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12644383719424 to 12781822672896 *)
Lemma J0092 : job_ok 137438953472 11606372338535 1 45293355392788 6943366945354 2 50574834910937.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6943366945354 2 50574834910937))]. Qed.
