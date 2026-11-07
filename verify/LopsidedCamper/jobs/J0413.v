From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 56762287783936 to 56899726737408 *)
Lemma J0413 : job_ok 137438953472 92360317664239 1 163069977047821 134082567316737 1 121966202497973.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 134082567316737 1 121966202497973))]. Qed.
