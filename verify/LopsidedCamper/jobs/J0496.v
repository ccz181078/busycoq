From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68169720922112 to 68307159875584 *)
Lemma J0496 : job_ok 137438953472 76228202198515 1 230535542908888 33296897097407 1 274085323564425.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 33296897097407 1 274085323564425))]. Qed.
