From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54838142435328 to 54975581388800 *)
Lemma J0399 : job_ok 137438953472 164722741803226 2 82048900261859 23867922632827 1 223522194475052.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 23867922632827 1 223522194475052))]. Qed.
