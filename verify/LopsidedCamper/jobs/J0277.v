From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38070590111744 to 38208029065216 *)
Lemma J0277 : job_ok 137438953472 53984199125064 2 117333451510000 31904158701979 1 140031966600054.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31904158701979 1 140031966600054))]. Qed.
