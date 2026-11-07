From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47966194761728 to 48103633715200 *)
Lemma J0349 : job_ok 137438953472 187920221807775 1 27927653670627 162445382942747 1 54020967691224.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 162445382942747 1 54020967691224))]. Qed.
