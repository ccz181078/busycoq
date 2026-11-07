From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63084479643648 to 63221918597120 *)
Lemma J0459 : job_ok 137438953472 275384654460963 1 8495501951593 135746148393963 1 148752483662370.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 135746148393963 1 148752483662370))]. Qed.
