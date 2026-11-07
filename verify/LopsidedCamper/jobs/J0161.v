From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22127671508992 to 22265110462464 *)
Lemma J0161 : job_ok 137438953472 55135489047027 1 44439029751255 91783828983145 1 8409164660925.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 91783828983145 1 8409164660925))]. Qed.
