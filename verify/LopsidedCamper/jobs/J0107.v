From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14705968021504 to 14843406974976 *)
Lemma J0107 : job_ok 137438953472 18067669919514 2 48109185619405 41430102652851 1 25365227416848.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 41430102652851 1 25365227416848))]. Qed.
