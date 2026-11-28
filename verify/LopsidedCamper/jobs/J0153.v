From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21028159881216 to 21165598834688 *)
Lemma J0153 : job_ok 137438953472 2417415609849 1 92209299328667 49065254522002 2 46179935928375.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 49065254522002 2 46179935928375))]. Qed.
