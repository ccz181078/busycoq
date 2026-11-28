From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 12369505812480 to 12506944765952 *)
Lemma J0090 : job_ok 137438953472 3808782626411 1 51853993928485 24776919233895 1 31504333427335.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24776919233895 1 31504333427335))]. Qed.
