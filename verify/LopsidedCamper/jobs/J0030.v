From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4123168604160 to 4260607557632 *)
Lemma J0030 : job_ok 137438953472 11436468006043 1 7117790191295 12202592116683 1 6970141175305.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 12202592116683 1 6970141175305))]. Qed.
