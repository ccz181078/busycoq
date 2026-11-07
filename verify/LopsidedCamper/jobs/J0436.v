From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59923383713792 to 60060822667264 *)
Lemma J0436 : job_ok 137438953472 126155747926089 1 143499476496319 216527461199185 1 53746238941455.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 216527461199185 1 53746238941455))]. Qed.
