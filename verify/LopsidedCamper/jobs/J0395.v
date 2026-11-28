From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 54288386621440 to 54425825574912 *)
Lemma J0395 : job_ok 137438953472 23808147054421 1 220489593414711 107611848396433 1 137304368458542.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 107611848396433 1 137304368458542))]. Qed.
