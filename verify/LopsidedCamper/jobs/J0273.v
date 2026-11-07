From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 37520834297856 to 37658273251328 *)
Lemma J0273 : job_ok 137438953472 3154745360290 2 165689004043033 118123540033047 1 51338684734827.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 118123540033047 1 51338684734827))]. Qed.
