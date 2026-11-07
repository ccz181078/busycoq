From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 36971078483968 to 37108517437440 *)
Lemma J0269 : job_ok 137438953472 122183004507208 2 44186844062660 98502950486989 1 68485373212962.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98502950486989 1 68485373212962))]. Qed.
