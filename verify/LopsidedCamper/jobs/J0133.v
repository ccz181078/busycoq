From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18279380811776 to 18416819765248 *)
Lemma J0133 : job_ok 137438953472 21379661341266 2 60877554015220 65709605638955 1 17166084748051.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 65709605638955 1 17166084748051))]. Qed.
