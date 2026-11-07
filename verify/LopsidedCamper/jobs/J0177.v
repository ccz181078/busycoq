From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24326694764544 to 24464133718016 *)
Lemma J0177 : job_ok 137438953472 62884510100979 1 46585612318440 82871688355667 1 27216909691275.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 82871688355667 1 27216909691275))]. Qed.
