From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28037546508288 to 28174985461760 *)
Lemma J0204 : job_ok 137438953472 21374708265986 2 104794245886640 115705070646915 1 11082358665821.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 115705070646915 1 11082358665821))]. Qed.
