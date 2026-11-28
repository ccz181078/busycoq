From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49203145342976 to 49340584296448 *)
Lemma J0358 : job_ok 137438953472 33595748814905 1 187818404572310 188861791031082 2 33170838070337.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 188861791031082 2 33170838070337))]. Qed.
