From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34084860461056 to 34222299414528 *)
Lemma J0248 : job_ok 137438953472 82704614452795 1 70677251793037 34601901009293 1 119398440934496.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34601901009293 1 119398440934496))]. Qed.
