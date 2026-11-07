From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32160715112448 to 32298154065920 *)
Lemma J0234 : job_ok 137438953472 56417717641129 1 88305495446538 36889740729666 2 108451947525485.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 36889740729666 2 108451947525485))]. Qed.
