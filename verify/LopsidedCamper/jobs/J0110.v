From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15118284881920 to 15255723835392 *)
Lemma J0110 : job_ok 137438953472 34407642710281 1 33624638068593 31156739194863 1 37494016705517.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31156739194863 1 37494016705517))]. Qed.
