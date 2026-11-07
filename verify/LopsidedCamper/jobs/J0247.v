From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33947421507584 to 34084860461056 *)
Lemma J0247 : job_ok 137438953472 50811527066346 2 101951863790715 82704614452795 1 70677251793037.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 82704614452795 1 70677251793037))]. Qed.
