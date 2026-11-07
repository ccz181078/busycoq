From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54563264528384 to 54700703481856 *)
Lemma J0397 : job_ok 137438953472 78125951969602 2 167408740223211 21738928611607 1 224414238767191.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21738928611607 1 224414238767191))]. Qed.
