From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 30648886624256 to 30786325577728 *)
Lemma J0223 : job_ok 137438953472 66702912986301 1 71217072834522 126829215019581 1 11709245927250.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 126829215019581 1 11709245927250))]. Qed.
