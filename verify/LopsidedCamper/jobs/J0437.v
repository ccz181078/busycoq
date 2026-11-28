From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60060822667264 to 60198261620736 *)
Lemma J0437 : job_ok 137438953472 216527461199185 1 53746238941455 159288102618737 1 111604072288083.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 159288102618737 1 111604072288083))]. Qed.
