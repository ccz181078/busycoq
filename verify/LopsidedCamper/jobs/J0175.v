From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24051816857600 to 24189255811072 *)
Lemma J0175 : job_ok 137438953472 35865707395495 1 72367464079600 18991325608419 1 89860320992474.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 18991325608419 1 89860320992474))]. Qed.
