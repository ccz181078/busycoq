From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16904991277056 to 17042430230528 *)
Lemma J0123 : job_ok 137438953472 22722938111043 1 53349524488392 52805038843341 1 23885898724606.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 52805038843341 1 23885898724606))]. Qed.
