From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 25151328485376 to 25288767438848 *)
Lemma J0183 : job_ok 137438953472 88775042228159 1 24405932697941 24134555985349 1 89664893913282.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24134555985349 1 89664893913282))]. Qed.
