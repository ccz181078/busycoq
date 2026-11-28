From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 1649267441664 to 1786706395136 *)
Lemma J0012 : job_ok 137438953472 5649816479647 1 1771886193675 4517005138283 1 3523173390350.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4517005138283 1 3523173390350))]. Qed.
