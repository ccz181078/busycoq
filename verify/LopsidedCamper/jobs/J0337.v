From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46316927320064 to 46454366273536 *)
Lemma J0337 : job_ok 137438953472 45209925493293 1 163216246325639 46807682676361 1 162236964991829.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 46807682676361 1 162236964991829))]. Qed.
