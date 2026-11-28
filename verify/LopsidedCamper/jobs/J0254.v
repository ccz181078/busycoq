From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34909494181888 to 35046933135360 *)
Lemma J0254 : job_ok 137438953472 22522982709417 1 134569736802139 3111993394047 1 154599201513165.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3111993394047 1 154599201513165))]. Qed.
