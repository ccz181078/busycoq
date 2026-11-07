From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6597069766656 to 6734508720128 *)
Lemma J0048 : job_ok 137438953472 18565310764034 2 11121499612095 18977088666595 1 11328197267533.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 18977088666595 1 11328197267533))]. Qed.
