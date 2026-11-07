From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 10720238370816 to 10857677324288 *)
Lemma J0078 : job_ok 137438953472 24390832151039 1 23850242765976 21888315842951 1 26971233865771.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 21888315842951 1 26971233865771))]. Qed.
