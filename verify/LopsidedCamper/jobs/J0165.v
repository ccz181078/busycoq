From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22677427322880 to 22814866276352 *)
Lemma J0165 : job_ok 137438953472 91695592225175 1 10352827360829 40593083354057 1 62073811328659.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 40593083354057 1 62073811328659))]. Qed.
