From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65420941852672 to 65558380806144 *)
Lemma J0476 : job_ok 137438953472 215851358422379 1 78542879266848 68683935004983 1 226328777988471.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 68683935004983 1 226328777988471))]. Qed.
