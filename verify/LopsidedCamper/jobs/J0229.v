From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31473520345088 to 31610959298560 *)
Lemma J0229 : job_ok 137438953472 55897845144890 2 85732991583987 14692580597373 1 127556731473756.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 14692580597373 1 127556731473756))]. Qed.
