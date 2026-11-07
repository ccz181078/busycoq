From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3435973836800 to 3573412790272 *)
Lemma J0025 : job_ok 137438953472 5229889987169 1 10231992332633 7680125818755 1 8400232693111.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 7680125818755 1 8400232693111))]. Qed.
