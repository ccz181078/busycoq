From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22952305229824 to 23089744183296 *)
Lemma J0167 : job_ok 137438953472 99541826442259 1 3743543209949 98597935393298 2 5305909046947.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98597935393298 2 5305909046947))]. Qed.
