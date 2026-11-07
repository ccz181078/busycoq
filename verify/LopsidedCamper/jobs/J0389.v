From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53463752900608 to 53601191854080 *)
Lemma J0389 : job_ok 137438953472 59911952076954 2 180674935953287 137899208611521 1 103306154279007.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 137899208611521 1 103306154279007))]. Qed.
