From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50165218017280 to 50302656970752 *)
Lemma J0365 : job_ok 137438953472 126434850600674 2 99308630853790 69059756916757 1 157302200034095.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 69059756916757 1 157302200034095))]. Qed.
