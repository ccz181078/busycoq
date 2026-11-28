From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 40132174413824 to 40269613367296 *)
Lemma J0292 : job_ok 137438953472 74246259132251 1 106348521270680 67399341563881 1 113813914178297.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 67399341563881 1 113813914178297))]. Qed.
