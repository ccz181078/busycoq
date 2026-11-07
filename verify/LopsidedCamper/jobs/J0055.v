From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 7559142440960 to 7696581394432 *)
Lemma J0055 : job_ok 137438953472 3126558403536 2 30889581315951 5579191609818 2 29055423039168.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5579191609818 2 29055423039168))]. Qed.
