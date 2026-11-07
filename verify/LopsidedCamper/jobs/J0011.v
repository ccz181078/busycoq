From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1511828488192 to 1649267441664 *)
Lemma J0011 : job_ok 137438953472 3370487406417 1 3432740026240 5649816479647 1 1771886193675.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5649816479647 1 1771886193675))]. Qed.
