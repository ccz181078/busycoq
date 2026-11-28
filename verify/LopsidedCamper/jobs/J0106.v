From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14568529068032 to 14705968021504 *)
Lemma J0106 : job_ok 137438953472 23440152488075 1 42118227472482 18067669919514 2 48109185619405.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 18067669919514 2 48109185619405))]. Qed.
