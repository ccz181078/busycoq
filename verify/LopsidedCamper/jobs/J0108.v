From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14843406974976 to 14980845928448 *)
Lemma J0108 : job_ok 137438953472 41430102652851 1 25365227416848 26872061753223 1 40541743942027.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 26872061753223 1 40541743942027))]. Qed.
