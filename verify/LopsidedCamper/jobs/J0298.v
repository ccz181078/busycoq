From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40956808134656 to 41094247088128 *)
Lemma J0298 : job_ok 137438953472 8606040832418 2 175699590541902 151878592684475 1 33045514250007.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 151878592684475 1 33045514250007))]. Qed.
