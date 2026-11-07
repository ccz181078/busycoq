From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62809601736704 to 62947040690176 *)
Lemma J0457 : job_ok 137438953472 140461009698631 1 142182195671751 73681771729466 2 209579909167914.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 73681771729466 2 209579909167914))]. Qed.
