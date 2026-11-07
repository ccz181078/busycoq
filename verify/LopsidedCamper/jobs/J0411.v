From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56487409876992 to 56624848830464 *)
Lemma J0411 : job_ok 137438953472 97329537171139 1 156863807074196 132805391401553 1 122006428162051.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 132805391401553 1 122006428162051))]. Qed.
