From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 59236188946432 to 59373627899904 *)
Lemma J0431 : job_ok 137438953472 73738938664658 2 192823909522479 97407226558929 1 169774096990617.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 97407226558929 1 169774096990617))]. Qed.
