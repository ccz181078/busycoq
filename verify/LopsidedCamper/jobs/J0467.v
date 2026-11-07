From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 64183991271424 to 64321430224896 *)
Lemma J0467 : job_ok 137438953472 80687130465794 2 208140829132243 268719538879087 1 20726896277080.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 268719538879087 1 20726896277080))]. Qed.
