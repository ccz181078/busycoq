From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28174985461760 to 28312424415232 *)
Lemma J0205 : job_ok 137438953472 115705070646915 1 11082358665821 14275068832251 1 113130836287998.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 14275068832251 1 113130836287998))]. Qed.
