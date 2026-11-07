From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29549374996480 to 29686813949952 *)
Lemma J0215 : job_ok 137438953472 69480063215535 1 63492118656780 9872080931219 1 123718576938136.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9872080931219 1 123718576938136))]. Qed.
