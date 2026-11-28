From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44667659878400 to 44805098831872 *)
Lemma J0325 : job_ok 137438953472 69735692809371 1 131268773807387 166603447928525 1 35019494463032.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 166603447928525 1 35019494463032))]. Qed.
