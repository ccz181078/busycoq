From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 55662776156160 to 55800215109632 *)
Lemma J0405 : job_ok 137438953472 116239308302922 2 134243185097417 97449835352425 1 153651132660749.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 97449835352425 1 153651132660749))]. Qed.
