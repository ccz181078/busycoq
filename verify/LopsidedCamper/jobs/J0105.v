From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 14431090114560 to 14568529068032 *)
Lemma J0105 : job_ok 137438953472 20892215592629 1 44047689547280 23440152488075 1 42118227472482.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 23440152488075 1 42118227472482))]. Qed.
