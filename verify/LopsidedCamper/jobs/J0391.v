From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53738630807552 to 53876069761024 *)
Lemma J0391 : job_ok 137438953472 78991222343165 1 162832615569314 104684409352583 1 137757903931868.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 104684409352583 1 137757903931868))]. Qed.
