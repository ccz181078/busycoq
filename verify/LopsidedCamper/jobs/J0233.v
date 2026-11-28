From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 32023276158976 to 32160715112448 *)
Lemma J0233 : job_ok 137438953472 109398697240733 1 34706041059948 56417717641129 1 88305495446538.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 56417717641129 1 88305495446538))]. Qed.
