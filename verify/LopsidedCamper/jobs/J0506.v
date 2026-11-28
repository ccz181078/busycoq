From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69544110456832 to 69681549410304 *)
Lemma J0506 : job_ok 137438953472 107952239176849 1 204996259319945 209602851599793 1 103964122270171.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 209602851599793 1 103964122270171))]. Qed.
