From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38208029065216 to 38345468018688 *)
Lemma J0278 : job_ok 137438953472 31904158701979 1 140031966600054 52908743457591 1 119645856522464.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 52908743457591 1 119645856522464))]. Qed.
