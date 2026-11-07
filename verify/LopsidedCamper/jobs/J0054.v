From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7421703487488 to 7559142440960 *)
Lemma J0054 : job_ok 137438953472 11645099505482 2 21752563866817 3126558403536 2 30889581315951.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3126558403536 2 30889581315951))]. Qed.
