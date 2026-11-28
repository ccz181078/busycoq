From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25563645345792 to 25701084299264 *)
Lemma J0186 : job_ok 137438953472 57706778413511 1 57329621951737 101383842974327 1 14271032686156.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 101383842974327 1 14271032686156))]. Qed.
