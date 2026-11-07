From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 824633720832 to 962072674304 *)
Lemma J0006 : job_ok 137438953472 76617530146 2 3634234028893 1418253431287 1 2911073130399.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1418253431287 1 2911073130399))]. Qed.
