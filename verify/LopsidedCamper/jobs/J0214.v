From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29411936043008 to 29549374996480 *)
Lemma J0214 : job_ok 137438953472 2837391745737 1 129516314405667 69480063215535 1 63492118656780.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 69480063215535 1 63492118656780))]. Qed.
