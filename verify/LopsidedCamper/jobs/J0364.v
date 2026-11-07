From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50027779063808 to 50165218017280 *)
Lemma J0364 : job_ok 137438953472 55716822922193 1 169408183506617 126434850600674 2 99308630853790.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 126434850600674 2 99308630853790))]. Qed.
