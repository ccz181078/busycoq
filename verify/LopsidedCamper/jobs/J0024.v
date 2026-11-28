From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3298534883328 to 3435973836800 *)
Lemma J0024 : job_ok 137438953472 7224124137629 1 7619283053996 5229889987169 1 10231992332633.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5229889987169 1 10231992332633))]. Qed.
