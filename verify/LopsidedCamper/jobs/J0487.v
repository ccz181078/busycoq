From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66932770340864 to 67070209294336 *)
Lemma J0487 : job_ok 137438953472 51718901289314 2 249478567613765 272643948706751 1 29171994956873.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 272643948706751 1 29171994956873))]. Qed.
