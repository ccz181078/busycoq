From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64458869178368 to 64596308131840 *)
Lemma J0469 : job_ok 137438953472 151494268137227 1 138570642484987 247780565415402 2 42902820325917.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 247780565415402 2 42902820325917))]. Qed.
