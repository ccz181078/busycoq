From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8796093022208 to 8933531975680 *)
Lemma J0064 : job_ok 137438953472 34102527041779 1 5479889484429 8695204894757 1 31505687138762.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 8695204894757 1 31505687138762))]. Qed.
