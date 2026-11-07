From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8521215115264 to 8658654068736 *)
Lemma J0062 : job_ok 137438953472 13166872415683 1 25178593794887 2130221401465 1 36833720330489.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 2130221401465 1 36833720330489))]. Qed.
