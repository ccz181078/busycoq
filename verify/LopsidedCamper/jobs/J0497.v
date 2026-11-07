From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 68307159875584 to 68444598829056 *)
Lemma J0497 : job_ok 137438953472 33296897097407 1 274085323564425 200308014528915 1 107692681197401.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 200308014528915 1 107692681197401))]. Qed.
