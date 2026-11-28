From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 61160334295040 to 61297773248512 *)
Lemma J0445 : job_ok 137438953472 133151850999459 1 142069650943708 248756240474797 1 27083736353946.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 248756240474797 1 27083736353946))]. Qed.
