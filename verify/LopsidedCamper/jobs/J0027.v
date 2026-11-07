From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3710851743744 to 3848290697216 *)
Lemma J0027 : job_ok 137438953472 13444669549075 1 3254164664168 10662592424629 1 6654716624406.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10662592424629 1 6654716624406))]. Qed.
