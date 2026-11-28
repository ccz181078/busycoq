From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 4672924418048 to 4810363371520 *)
Lemma J0034 : job_ok 137438953472 6344292002701 1 14683866701432 9000666487255 1 12645967532692.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9000666487255 1 12645967532692))]. Qed.
