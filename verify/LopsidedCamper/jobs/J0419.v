From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57586921504768 to 57724360458240 *)
Lemma J0419 : job_ok 137438953472 225678078065010 2 33463067983575 226850441911803 1 32909179476515.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 226850441911803 1 32909179476515))]. Qed.
