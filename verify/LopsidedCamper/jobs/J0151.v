From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20753281974272 to 20890720927744 *)
Lemma J0151 : job_ok 137438953472 44824171546827 1 48565594275265 16018431316267 1 77989808824057.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 16018431316267 1 77989808824057))]. Qed.
