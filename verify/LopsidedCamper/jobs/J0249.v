From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34222299414528 to 34359738368000 *)
Lemma J0249 : job_ok 137438953472 34601901009293 1 119398440934496 136105525023543 1 18513292317874.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 136105525023543 1 18513292317874))]. Qed.
