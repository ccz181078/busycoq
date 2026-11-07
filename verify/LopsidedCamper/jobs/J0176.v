From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24189255811072 to 24326694764544 *)
Lemma J0176 : job_ok 137438953472 18991325608419 1 89860320992474 62884510100979 1 46585612318440.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 62884510100979 1 46585612318440))]. Qed.
