From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24464133718016 to 24601572671488 *)
Lemma J0178 : job_ok 137438953472 82871688355667 1 27216909691275 8031222374365 1 102675851440278.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8031222374365 1 102675851440278))]. Qed.
