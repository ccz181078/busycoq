From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41781441855488 to 41918880808960 *)
Lemma J0304 : job_ok 137438953472 182694003042893 1 5322481007026 71709643213381 1 116925316504988.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 71709643213381 1 116925316504988))]. Qed.
