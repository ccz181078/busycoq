From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37108517437440 to 37245956390912 *)
Lemma J0270 : job_ok 137438953472 98502950486989 1 68485373212962 124506452275066 2 43100346990094.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 124506452275066 2 43100346990094))]. Qed.
