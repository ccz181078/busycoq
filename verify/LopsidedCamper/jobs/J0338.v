From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46454366273536 to 46591805227008 *)
Lemma J0338 : job_ok 137438953472 46807682676361 1 162236964991829 59195443153437 1 150467678745099.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 59195443153437 1 150467678745099))]. Qed.
