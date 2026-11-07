From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61022895341568 to 61160334295040 *)
Lemma J0444 : job_ok 137438953472 167781528154162 2 106821498464633 133151850999459 1 142069650943708.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 133151850999459 1 142069650943708))]. Qed.
