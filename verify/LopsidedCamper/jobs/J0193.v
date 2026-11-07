From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26525718020096 to 26663156973568 *)
Lemma J0193 : job_ok 137438953472 82332331712187 1 37033395623259 55778903518811 1 64205299778251.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 55778903518811 1 64205299778251))]. Qed.
