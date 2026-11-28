From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46866683133952 to 47004122087424 *)
Lemma J0341 : job_ok 137438953472 187319749408267 1 23580322660919 9475967758909 1 202042580165858.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 9475967758909 1 202042580165858))]. Qed.
