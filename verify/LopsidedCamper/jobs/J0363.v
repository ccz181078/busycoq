From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49890340110336 to 50027779063808 *)
Lemma J0363 : job_ok 137438953472 16822873632247 1 207683658179308 55716822922193 1 169408183506617.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 55716822922193 1 169408183506617))]. Qed.
