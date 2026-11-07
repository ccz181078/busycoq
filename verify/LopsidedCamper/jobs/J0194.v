From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26663156973568 to 26800595927040 *)
Lemma J0194 : job_ok 137438953472 55778903518811 1 64205299778251 31631949550351 1 88970729167273.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 31631949550351 1 88970729167273))]. Qed.
