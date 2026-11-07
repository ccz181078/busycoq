From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28862180229120 to 28999619182592 *)
Lemma J0210 : job_ok 137438953472 129286260698255 1 593544502340 129080930782512 2 1417349083370.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 129080930782512 2 1417349083370))]. Qed.
