From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71468255805440 to 71605694758912 *)
Lemma J0520 : job_ok 137438953472 184476995359834 2 137130154855298 296346816884503 1 25878808081107.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 296346816884503 1 25878808081107))]. Qed.
