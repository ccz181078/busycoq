From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50714973831168 to 50852412784640 *)
Lemma J0369 : job_ok 137438953472 196523086226047 1 31694297285635 160188179150769 1 68647679811294.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 160188179150769 1 68647679811294))]. Qed.
