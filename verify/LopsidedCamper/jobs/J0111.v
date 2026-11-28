From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15255723835392 to 15393162788864 *)
Lemma J0111 : job_ok 137438953472 31156739194863 1 37494016705517 60021440046314 2 9247791873077.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 60021440046314 2 9247791873077))]. Qed.
