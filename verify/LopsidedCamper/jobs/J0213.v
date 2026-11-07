From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29274497089536 to 29411936043008 *)
Lemma J0213 : job_ok 137438953472 98079662006937 1 33655568347535 2837391745737 1 129516314405667.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2837391745737 1 129516314405667))]. Qed.
