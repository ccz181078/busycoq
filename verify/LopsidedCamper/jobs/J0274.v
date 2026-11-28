From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37658273251328 to 37795712204800 *)
Lemma J0274 : job_ok 137438953472 118123540033047 1 51338684734827 64717795511333 1 105362904298378.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 64717795511333 1 105362904298378))]. Qed.
