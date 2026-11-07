From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32298154065920 to 32435593019392 *)
Lemma J0235 : job_ok 137438953472 36889740729666 2 108451947525485 109064478827149 1 36895685111706.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 109064478827149 1 36895685111706))]. Qed.
