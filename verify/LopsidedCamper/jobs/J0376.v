From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51677046505472 to 51814485458944 *)
Lemma J0376 : job_ok 137438953472 26586924014147 1 205959786735254 171555205773490 2 61609980038032.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 171555205773490 2 61609980038032))]. Qed.
