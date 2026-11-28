From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20890720927744 to 21028159881216 *)
Lemma J0152 : job_ok 137438953472 16018431316267 1 77989808824057 2417415609849 1 92209299328667.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2417415609849 1 92209299328667))]. Qed.
