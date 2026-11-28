From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23914377904128 to 24051816857600 *)
Lemma J0174 : job_ok 137438953472 71842363319069 1 35772332811008 35865707395495 1 72367464079600.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 35865707395495 1 72367464079600))]. Qed.
