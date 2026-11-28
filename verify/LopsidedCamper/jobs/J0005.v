From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 687194767360 to 824633720832 *)
Lemma J0005 : job_ok 137438953472 1453896559715 1 1638479380020 76617530146 2 3634234028893.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 76617530146 2 3634234028893))]. Qed.
