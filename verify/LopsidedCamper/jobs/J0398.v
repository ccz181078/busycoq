From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54700703481856 to 54838142435328 *)
Lemma J0398 : job_ok 137438953472 21738928611607 1 224414238767191 164722741803226 2 82048900261859.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 164722741803226 2 82048900261859))]. Qed.
