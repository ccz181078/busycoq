From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26388279066624 to 26525718020096 *)
Lemma J0192 : job_ok 137438953472 42734894837603 1 76012357030938 82332331712187 1 37033395623259.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 82332331712187 1 37033395623259))]. Qed.
