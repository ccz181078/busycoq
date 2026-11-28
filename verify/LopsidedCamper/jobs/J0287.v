From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39444979646464 to 39582418599936 *)
Lemma J0287 : job_ok 137438953472 137879562576259 1 39622841781052 107232449416337 1 70888430699177.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 107232449416337 1 70888430699177))]. Qed.
