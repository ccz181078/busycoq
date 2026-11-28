From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20066087206912 to 20203526160384 *)
Lemma J0146 : job_ok 137438953472 74118795152539 1 16178594439862 79227738566579 1 11688126762401.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 79227738566579 1 11688126762401))]. Qed.
