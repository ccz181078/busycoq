From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32435593019392 to 32573031972864 *)
Lemma J0236 : job_ok 137438953472 109064478827149 1 36895685111706 143129244934298 2 3449393729055.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 143129244934298 2 3449393729055))]. Qed.
