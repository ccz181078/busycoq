From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 53326313947136 to 53463752900608 *)
Lemma J0388 : job_ok 137438953472 127264274369113 1 112704138553441 59911952076954 2 180674935953287.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 59911952076954 2 180674935953287))]. Qed.
