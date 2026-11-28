From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57449482551296 to 57586921504768 *)
Lemma J0418 : job_ok 137438953472 165435818822517 1 93086852302422 225678078065010 2 33463067983575.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 225678078065010 2 33463067983575))]. Qed.
