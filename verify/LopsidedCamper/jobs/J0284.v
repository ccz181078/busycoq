From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39032662786048 to 39170101739520 *)
Lemma J0284 : job_ok 137438953472 85343706716762 2 90303270659220 136619650022303 1 39645803462605.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 136619650022303 1 39645803462605))]. Qed.
