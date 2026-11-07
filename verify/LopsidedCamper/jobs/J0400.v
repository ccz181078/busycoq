From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54975581388800 to 55113020342272 *)
Lemma J0400 : job_ok 137438953472 23867922632827 1 223522194475052 62544637580197 1 185463954834552.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 62544637580197 1 185463954834552))]. Qed.
