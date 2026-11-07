From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22814866276352 to 22952305229824 *)
Lemma J0166 : job_ok 137438953472 40593083354057 1 62073811328659 99541826442259 1 3743543209949.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 99541826442259 1 3743543209949))]. Qed.
