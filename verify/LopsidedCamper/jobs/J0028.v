From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3848290697216 to 3985729650688 *)
Lemma J0028 : job_ok 137438953472 10662592424629 1 6654716624406 4039513774371 1 13896269395025.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4039513774371 1 13896269395025))]. Qed.
