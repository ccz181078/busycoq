From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53051436040192 to 53188874993664 *)
Lemma J0386 : job_ok 137438953472 13463191896018 2 225268270259756 29364453560258 2 209985484304215.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 29364453560258 2 209985484304215))]. Qed.
