From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 34772055228416 to 34909494181888 *)
Lemma J0253 : job_ok 137438953472 5148675474675 1 151325568405826 22522982709417 1 134569736802139.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 22522982709417 1 134569736802139))]. Qed.
