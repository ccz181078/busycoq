From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 8658654068736 to 8796093022208 *)
Lemma J0063 : job_ok 137438953472 2130221401465 1 36833720330489 34102527041779 1 5479889484429.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 34102527041779 1 5479889484429))]. Qed.
