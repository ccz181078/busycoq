From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 13056700579840 to 13194139533312 *)
Lemma J0095 : job_ok 137438953472 44234081252413 1 14521072078742 2296994705311 1 57076633206018.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2296994705311 1 57076633206018))]. Qed.
