From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54425825574912 to 54563264528384 *)
Lemma J0396 : job_ok 137438953472 107611848396433 1 137304368458542 78125951969602 2 167408740223211.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 78125951969602 2 167408740223211))]. Qed.
