From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7009386627072 to 7146825580544 *)
Lemma J0051 : job_ok 137438953472 17812492468569 1 13729744438269 9893546954768 2 22267164827984.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9893546954768 2 22267164827984))]. Qed.
