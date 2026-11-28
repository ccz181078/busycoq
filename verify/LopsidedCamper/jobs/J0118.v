From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 16217796509696 to 16355235463168 *)
Lemma J0118 : job_ok 137438953472 10775715738601 1 62204368585319 63696777417981 1 9901782639765.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 63696777417981 1 9901782639765))]. Qed.
