From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34359738368000 to 34497177321472 *)
Lemma J0250 : job_ok 137438953472 136105525023543 1 18513292317874 6613969887799 1 148623322406178.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 6613969887799 1 148623322406178))]. Qed.
