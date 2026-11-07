From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41506563948544 to 41644002902016 *)
Lemma J0302 : job_ok 137438953472 8697514351577 1 178082018488615 120754912456017 1 66643095866609.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 120754912456017 1 66643095866609))]. Qed.
