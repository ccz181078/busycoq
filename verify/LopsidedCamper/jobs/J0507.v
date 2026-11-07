From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69681549410304 to 69818988363776 *)
Lemma J0507 : job_ok 137438953472 209602851599793 1 103964122270171 219559420913619 1 94626028154588.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 219559420913619 1 94626028154588))]. Qed.
