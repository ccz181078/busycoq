From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7696581394432 to 7834020347904 *)
Lemma J0056 : job_ok 137438953472 5579191609818 2 29055423039168 21117873607922 2 14135216662086.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21117873607922 2 14135216662086))]. Qed.
