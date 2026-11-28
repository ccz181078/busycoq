From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 71055938945024 to 71193377898496 *)
Lemma J0517 : job_ok 137438953472 286885484609813 1 32866240392269 184213800276771 1 136156399561455.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 184213800276771 1 136156399561455))]. Qed.
