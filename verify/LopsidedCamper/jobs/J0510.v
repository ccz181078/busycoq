From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 70093866270720 to 70231305224192 *)
Lemma J0510 : job_ok 137438953472 185158256960187 1 130264142257912 174759916054617 1 141280958646527.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 174759916054617 1 141280958646527))]. Qed.
