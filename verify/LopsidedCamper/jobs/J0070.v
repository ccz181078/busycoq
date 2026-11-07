From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 9620726743040 to 9758165696512 *)
Lemma J0070 : job_ok 137438953472 8240762247013 1 35052508064278 5735564395635 1 38176181745512.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5735564395635 1 38176181745512))]. Qed.
