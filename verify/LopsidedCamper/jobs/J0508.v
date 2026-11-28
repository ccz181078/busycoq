From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69818988363776 to 69956427317248 *)
Lemma J0508 : job_ok 137438953472 219559420913619 1 94626028154588 308059140793915 1 6744783585304.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 308059140793915 1 6744783585304))]. Qed.
