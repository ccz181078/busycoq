From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57174604644352 to 57312043597824 *)
Lemma J0416 : job_ok 137438953472 150563805156567 1 106721914672943 173197623546999 1 84706571250144.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 173197623546999 1 84706571250144))]. Qed.
