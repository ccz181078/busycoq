From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39307540692992 to 39444979646464 *)
Lemma J0286 : job_ok 137438953472 67505018949583 1 109378910268130 137879562576259 1 39622841781052.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 137879562576259 1 39622841781052))]. Qed.
