From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64321430224896 to 64458869178368 *)
Lemma J0468 : job_ok 137438953472 268719538879087 1 20726896277080 151494268137227 1 138570642484987.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 151494268137227 1 138570642484987))]. Qed.
