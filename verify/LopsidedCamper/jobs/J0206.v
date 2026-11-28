From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 28312424415232 to 28449863368704 *)
Lemma J0206 : job_ok 137438953472 14275068832251 1 113130836287998 87033199528543 1 40991180437416.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 87033199528543 1 40991180437416))]. Qed.
