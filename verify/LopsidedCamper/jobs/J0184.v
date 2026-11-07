From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25288767438848 to 25426206392320 *)
Lemma J0184 : job_ok 137438953472 24134555985349 1 89664893913282 100578524190480 2 13839401165925.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 100578524190480 2 13839401165925))]. Qed.
