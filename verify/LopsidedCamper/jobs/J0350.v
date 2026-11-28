From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48103633715200 to 48241072668672 *)
Lemma J0350 : job_ok 137438953472 162445382942747 1 54020967691224 63329955569731 1 153754870314985.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 63329955569731 1 153754870314985))]. Qed.
