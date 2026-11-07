From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 3573412790272 to 3710851743744 *)
Lemma J0026 : job_ok 137438953472 7680125818755 1 8400232693111 13444669549075 1 3254164664168.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 13444669549075 1 3254164664168))]. Qed.
