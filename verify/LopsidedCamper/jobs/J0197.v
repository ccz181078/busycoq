From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27075473833984 to 27212912787456 *)
Lemma J0197 : job_ok 137438953472 83352251940639 1 38487376615970 77890737667471 1 44567365926735.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 77890737667471 1 44567365926735))]. Qed.
