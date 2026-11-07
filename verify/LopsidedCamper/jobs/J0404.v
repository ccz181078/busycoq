From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55525337202688 to 55662776156160 *)
Lemma J0404 : job_ok 137438953472 121320331184975 1 128543687174916 116239308302922 2 134243185097417.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 116239308302922 2 134243185097417))]. Qed.
