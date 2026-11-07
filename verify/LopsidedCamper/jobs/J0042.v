From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5772436045824 to 5909874999296 *)
Lemma J0042 : job_ok 137438953472 23263147479449 1 2712813072687 13754716583843 1 12839718978107.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13754716583843 1 12839718978107))]. Qed.
