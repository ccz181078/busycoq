From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38482906972160 to 38620345925632 *)
Lemma J0280 : job_ok 137438953472 128572099912667 1 44600975535687 48021675556435 1 125769875157208.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 48021675556435 1 125769875157208))]. Qed.
