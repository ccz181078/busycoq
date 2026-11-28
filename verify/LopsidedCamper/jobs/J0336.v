From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 46179488366592 to 46316927320064 *)
Lemma J0336 : job_ok 137438953472 20636839707083 1 187170856803031 45209925493293 1 163216246325639.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 45209925493293 1 163216246325639))]. Qed.
