From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71743133712384 to the halt at 71755048174256: the step from map step 71755048174256 returns Halt *)
Lemma J0522 : job_halt 11914461873 258246047606674 2 64598052849462.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl Halt)]. Qed.
