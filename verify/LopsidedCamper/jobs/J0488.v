From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 67070209294336 to 67207648247808 *)
Lemma J0488 : job_ok 137438953472 272643948706751 1 29171994956873 259424513729883 1 43009904831109.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 259424513729883 1 43009904831109))]. Qed.
