From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12094627905536 to 12232066859008 *)
Lemma J0088 : job_ok 137438953472 5704451007373 1 48721375934753 38042648188671 1 17001653725731.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 38042648188671 1 17001653725731))]. Qed.
