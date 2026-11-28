From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41231686041600 to 41369124995072 *)
Lemma J0300 : job_ok 137438953472 11775551411231 1 173767030828864 86274871111887 1 99886186049282.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 86274871111887 1 99886186049282))]. Qed.
