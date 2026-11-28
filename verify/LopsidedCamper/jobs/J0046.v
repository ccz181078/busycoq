From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 6322191859712 to 6459630813184 *)
Lemma J0046 : job_ok 137438953472 1156589690869 1 27293270574670 11738310889751 1 17330024875731.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11738310889751 1 17330024875731))]. Qed.
