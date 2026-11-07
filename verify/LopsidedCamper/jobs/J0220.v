From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30236569763840 to 30374008717312 *)
Lemma J0220 : job_ok 137438953472 43336058476805 1 92728501320786 90749045043885 1 45933990097970.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 90749045043885 1 45933990097970))]. Qed.
