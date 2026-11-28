From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22539988369408 to 22677427322880 *)
Lemma J0164 : job_ok 137438953472 82462532523760 2 18967410947065 91695592225175 1 10352827360829.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 91695592225175 1 10352827360829))]. Qed.
