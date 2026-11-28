From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 63221918597120 to 63359357550592 *)
Lemma J0460 : job_ok 137438953472 135746148393963 1 148752483662370 37204526581657 1 247912581067121.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 37204526581657 1 247912581067121))]. Qed.
