From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 41094247088128 to 41231686041600 *)
Lemma J0299 : job_ok 137438953472 151878592684475 1 33045514250007 11775551411231 1 173767030828864.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 11775551411231 1 173767030828864))]. Qed.
