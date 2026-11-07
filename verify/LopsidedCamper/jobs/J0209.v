From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28724741275648 to 28862180229120 *)
Lemma J0209 : job_ok 137438953472 4090332330277 1 125170997956810 129286260698255 1 593544502340.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 129286260698255 1 593544502340))]. Qed.
