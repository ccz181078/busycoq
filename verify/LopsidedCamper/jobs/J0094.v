From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12919261626368 to 13056700579840 *)
Lemma J0094 : job_ok 137438953472 17304138916813 1 40832538753650 44234081252413 1 14521072078742.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 44234081252413 1 14521072078742))]. Qed.
