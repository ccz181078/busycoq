From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 33122787786752 to 33260226740224 *)
Lemma J0241 : job_ok 137438953472 49526083119343 1 99526457205961 103820239114517 1 45850776679104.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 103820239114517 1 45850776679104))]. Qed.
