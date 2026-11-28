From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21990232555520 to 22127671508992 *)
Lemma J0160 : job_ok 137438953472 10769208768811 1 88186834012122 55135489047027 1 44439029751255.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 55135489047027 1 44439029751255))]. Qed.
