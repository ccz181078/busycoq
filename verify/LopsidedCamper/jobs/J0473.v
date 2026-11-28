From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65008624992256 to 65146063945728 *)
Lemma J0473 : job_ok 137438953472 124178277373879 1 168360534279352 185827561507613 1 107329725415394.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 185827561507613 1 107329725415394))]. Qed.
