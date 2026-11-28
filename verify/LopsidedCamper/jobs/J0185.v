From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25426206392320 to 25563645345792 *)
Lemma J0185 : job_ok 137438953472 100578524190480 2 13839401165925 57706778413511 1 57329621951737.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 57706778413511 1 57329621951737))]. Qed.
