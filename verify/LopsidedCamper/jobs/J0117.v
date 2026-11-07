From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16080357556224 to 16217796509696 *)
Lemma J0117 : job_ok 137438953472 16879327626807 1 55482282105010 10775715738601 1 62204368585319.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10775715738601 1 62204368585319))]. Qed.
