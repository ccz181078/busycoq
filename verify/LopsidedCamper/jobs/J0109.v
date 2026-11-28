From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14980845928448 to 15118284881920 *)
Lemma J0109 : job_ok 137438953472 26872061753223 1 40541743942027 34407642710281 1 33624638068593.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34407642710281 1 33624638068593))]. Qed.
