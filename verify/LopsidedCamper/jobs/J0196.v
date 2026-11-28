From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 26938034880512 to 27075473833984 *)
Lemma J0196 : job_ok 137438953472 10616616787159 1 110604536799978 83352251940639 1 38487376615970.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 83352251940639 1 38487376615970))]. Qed.
