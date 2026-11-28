From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 52364241272832 to 52501680226304 *)
Lemma J0381 : job_ok 137438953472 226183349200537 1 9455735950651 163209103915755 1 73048457116519.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 163209103915755 1 73048457116519))]. Qed.
