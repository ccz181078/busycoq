From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 5497558138880 to 5634997092352 *)
Lemma J0040 : job_ok 137438953472 10916345146059 1 13822664752975 17518833947811 1 7838650827635.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 17518833947811 1 7838650827635))]. Qed.
