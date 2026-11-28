From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23089744183296 to 23227183136768 *)
Lemma J0168 : job_ok 137438953472 98597935393298 2 5305909046947 89035407501901 1 15486912470724.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 89035407501901 1 15486912470724))]. Qed.
