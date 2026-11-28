From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27212912787456 to 27350351740928 *)
Lemma J0198 : job_ok 137438953472 77890737667471 1 44567365926735 60533961892661 1 62542616698639.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 60533961892661 1 62542616698639))]. Qed.
