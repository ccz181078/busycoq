From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68994354642944 to 69131793596416 *)
Lemma J0502 : job_ok 137438953472 275817107242930 2 34657489797062 199978008770402 2 111115063519043.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 199978008770402 2 111115063519043))]. Qed.
