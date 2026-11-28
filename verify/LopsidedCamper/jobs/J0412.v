From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56624848830464 to 56762287783936 *)
Lemma J0412 : job_ok 137438953472 132805391401553 1 122006428162051 92360317664239 1 163069977047821.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 92360317664239 1 163069977047821))]. Qed.
