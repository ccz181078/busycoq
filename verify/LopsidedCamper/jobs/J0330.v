From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 45354854645760 to 45492293599232 *)
Lemma J0330 : job_ok 137438953472 196357903699789 1 7738939829569 68116619149768 2 136598699761096.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 68116619149768 2 136598699761096))]. Qed.
