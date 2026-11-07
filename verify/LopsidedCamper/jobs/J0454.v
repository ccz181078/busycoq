From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 62397284876288 to 62534723829760 *)
Lemma J0454 : job_ok 137438953472 273840380199469 1 6947400606350 5396198400719 1 276010056587490.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5396198400719 1 276010056587490))]. Qed.
