From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21852793602048 to 21990232555520 *)
Lemma J0159 : job_ok 137438953472 56615325799970 2 41722241429097 10769208768811 1 88186834012122.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 10769208768811 1 88186834012122))]. Qed.
