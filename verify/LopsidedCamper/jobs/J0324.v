From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44530220924928 to 44667659878400 *)
Lemma J0324 : job_ok 137438953472 99909078800547 1 100476911880268 69735692809371 1 131268773807387.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 69735692809371 1 131268773807387))]. Qed.
