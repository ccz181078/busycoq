From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68032281968640 to 68169720922112 *)
Lemma J0495 : job_ok 137438953472 34409389680667 1 271735879293740 76228202198515 1 230535542908888.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 76228202198515 1 230535542908888))]. Qed.
