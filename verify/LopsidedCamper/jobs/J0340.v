From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46729244180480 to 46866683133952 *)
Lemma J0340 : job_ok 137438953472 183189748922447 1 27091848107841 187319749408267 1 23580322660919.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 187319749408267 1 23580322660919))]. Qed.
