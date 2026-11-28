From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62672162783232 to 62809601736704 *)
Lemma J0456 : job_ok 137438953472 276457980030683 1 5566749848751 140461009698631 1 142182195671751.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 140461009698631 1 142182195671751))]. Qed.
