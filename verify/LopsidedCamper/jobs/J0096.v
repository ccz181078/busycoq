From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13194139533312 to 13331578486784 *)
Lemma J0096 : job_ok 137438953472 2296994705311 1 57076633206018 30144873882035 1 29847229209711.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 30144873882035 1 29847229209711))]. Qed.
