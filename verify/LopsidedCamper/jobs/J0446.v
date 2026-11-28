From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61297773248512 to 61435212201984 *)
Lemma J0446 : job_ok 137438953472 248756240474797 1 27083736353946 195062373769011 1 81396078705000.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 195062373769011 1 81396078705000))]. Qed.
