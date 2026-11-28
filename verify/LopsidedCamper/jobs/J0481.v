From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 66108136620032 to 66245575573504 *)
Lemma J0481 : job_ok 137438953472 149327596986983 1 148159018917497 192758943024619 1 105346148329073.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 192758943024619 1 105346148329073))]. Qed.
