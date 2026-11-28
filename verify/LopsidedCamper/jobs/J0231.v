From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 31748398252032 to 31885837205504 *)
Lemma J0231 : job_ok 137438953472 91286196057567 1 51581591044073 132070863803714 2 11415399109936.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 132070863803714 2 11415399109936))]. Qed.
