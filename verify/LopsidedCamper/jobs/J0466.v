From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64046552317952 to 64183991271424 *)
Lemma J0466 : job_ok 137438953472 24917390114957 1 263292093759032 80687130465794 2 208140829132243.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 80687130465794 2 208140829132243))]. Qed.
