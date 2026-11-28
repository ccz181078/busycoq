From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35046933135360 to 35184372088832 *)
Lemma J0255 : job_ok 137438953472 3111993394047 1 154599201513165 70709106253695 1 87620563977421.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 70709106253695 1 87620563977421))]. Qed.
