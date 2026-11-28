From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38345468018688 to 38482906972160 *)
Lemma J0279 : job_ok 137438953472 52908743457591 1 119645856522464 128572099912667 1 44600975535687.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 128572099912667 1 44600975535687))]. Qed.
