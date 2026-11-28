From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35596688949248 to 35734127902720 *)
Lemma J0259 : job_ok 137438953472 93863146900552 2 66321948867346 24552891356965 1 136250679602022.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24552891356965 1 136250679602022))]. Qed.
