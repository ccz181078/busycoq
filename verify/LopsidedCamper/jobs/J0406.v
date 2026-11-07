From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55800215109632 to 55937654063104 *)
Lemma J0406 : job_ok 137438953472 97449835352425 1 153651132660749 160180493458707 1 91538951013543.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 160180493458707 1 91538951013543))]. Qed.
