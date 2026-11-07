From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68444598829056 to 68582037782528 *)
Lemma J0498 : job_ok 137438953472 200308014528915 1 107692681197401 216546965671067 1 92072205075949.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 216546965671067 1 92072205075949))]. Qed.
