From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18829136625664 to 18966575579136 *)
Lemma J0137 : job_ok 137438953472 48298266485049 1 36432849173345 46487905122306 2 38861685894451.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 46487905122306 2 38861685894451))]. Qed.
