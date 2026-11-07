From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71605694758912 to 71743133712384 *)
Lemma J0521 : job_ok 137438953472 296346816884503 1 25878808081107 258246047606674 2 64598052849462.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 258246047606674 2 64598052849462))]. Qed.
