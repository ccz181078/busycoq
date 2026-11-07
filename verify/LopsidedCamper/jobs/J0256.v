From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35184372088832 to 35321811042304 *)
Lemma J0256 : job_ok 137438953472 70709106253695 1 87620563977421 136007475807954 2 22940669997466.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 136007475807954 2 22940669997466))]. Qed.
