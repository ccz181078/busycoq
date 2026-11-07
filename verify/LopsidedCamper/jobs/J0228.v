From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31336081391616 to 31473520345088 *)
Lemma J0228 : job_ok 137438953472 37952658836885 1 103059702495456 55897845144890 2 85732991583987.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 55897845144890 2 85732991583987))]. Qed.
