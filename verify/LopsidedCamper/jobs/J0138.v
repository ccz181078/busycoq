From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18966575579136 to 19104014532608 *)
Lemma J0138 : job_ok 137438953472 46487905122306 2 38861685894451 42309958869297 1 43658107431859.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 42309958869297 1 43658107431859))]. Qed.
