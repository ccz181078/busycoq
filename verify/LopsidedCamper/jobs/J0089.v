From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12232066859008 to 12369505812480 *)
Lemma J0089 : job_ok 137438953472 38042648188671 1 17001653725731 3808782626411 1 51853993928485.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3808782626411 1 51853993928485))]. Qed.
