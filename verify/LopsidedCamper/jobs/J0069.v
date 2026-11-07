From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9483287789568 to 9620726743040 *)
Lemma J0069 : job_ok 137438953472 41017063204605 1 1657731458899 8240762247013 1 35052508064278.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8240762247013 1 35052508064278))]. Qed.
