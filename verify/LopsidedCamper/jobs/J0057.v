From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7834020347904 to 7971459301376 *)
Lemma J0057 : job_ok 137438953472 21117873607922 2 14135216662086 13465758121271 1 22405807155856.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13465758121271 1 22405807155856))]. Qed.
