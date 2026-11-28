From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 15393162788864 to 15530601742336 *)
Lemma J0112 : job_ok 137438953472 60021440046314 2 9247791873077 53451730909107 1 16435976911448.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 53451730909107 1 16435976911448))]. Qed.
