From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 57724360458240 to 57861799411712 *)
Lemma J0420 : job_ok 137438953472 226850441911803 1 32909179476515 117681097437993 1 142696999725499.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 117681097437993 1 142696999725499))]. Qed.
