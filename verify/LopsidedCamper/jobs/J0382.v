From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52501680226304 to 52639119179776 *)
Lemma J0382 : job_ok 137438953472 163209103915755 1 73048457116519 225422167615395 1 11453868846747.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 225422167615395 1 11453868846747))]. Qed.
