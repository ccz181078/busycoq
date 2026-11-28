From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64871186038784 to 65008624992256 *)
Lemma J0472 : job_ok 137438953472 226904077791639 1 65016259321487 124178277373879 1 168360534279352.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 124178277373879 1 168360534279352))]. Qed.
