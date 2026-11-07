From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16630113370112 to 16767552323584 *)
Lemma J0121 : job_ok 137438953472 54911156144929 1 19924355671475 74760902479825 1 693085071501.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 74760902479825 1 693085071501))]. Qed.
