From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52226802319360 to 52364241272832 *)
Lemma J0380 : job_ok 137438953472 110627043212391 1 124393566850875 226183349200537 1 9455735950651.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 226183349200537 1 9455735950651))]. Qed.
