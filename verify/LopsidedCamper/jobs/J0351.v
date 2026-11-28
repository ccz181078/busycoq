From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 48241072668672 to 48378511622144 *)
Lemma J0351 : job_ok 137438953472 63329955569731 1 153754870314985 81788663948429 1 135914637311114.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 81788663948429 1 135914637311114))]. Qed.
