From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31885837205504 to 32023276158976 *)
Lemma J0232 : job_ok 137438953472 132070863803714 2 11415399109936 109398697240733 1 34706041059948.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 109398697240733 1 34706041059948))]. Qed.
