From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7284264534016 to 7421703487488 *)
Lemma J0053 : job_ok 137438953472 9935984435947 1 22843203368000 11645099505482 2 21752563866817.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11645099505482 2 21752563866817))]. Qed.
