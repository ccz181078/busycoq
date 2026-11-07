From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8383776161792 to 8521215115264 *)
Lemma J0061 : job_ok 137438953472 14340718471747 1 23386272617740 13166872415683 1 25178593794887.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13166872415683 1 25178593794887))]. Qed.
