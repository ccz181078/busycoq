From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18141941858304 to 18279380811776 *)
Lemma J0132 : job_ok 137438953472 4403108773827 1 77235631188135 21379661341266 2 60877554015220.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21379661341266 2 60877554015220))]. Qed.
