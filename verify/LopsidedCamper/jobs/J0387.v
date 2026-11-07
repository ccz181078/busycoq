From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53188874993664 to 53326313947136 *)
Lemma J0387 : job_ok 137438953472 29364453560258 2 209985484304215 127264274369113 1 112704138553441.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 127264274369113 1 112704138553441))]. Qed.
