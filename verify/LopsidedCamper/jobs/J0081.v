From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 11132555231232 to 11269994184704 *)
Lemma J0081 : job_ok 137438953472 46572961021329 1 3523539948021 31506128153203 1 19208847697131.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31506128153203 1 19208847697131))]. Qed.
