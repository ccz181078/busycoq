From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47004122087424 to 47141561040896 *)
Lemma J0342 : job_ok 137438953472 9475967758909 1 202042580165858 43714141988643 1 168422881102338.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 43714141988643 1 168422881102338))]. Qed.
