From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 22265110462464 to 22402549415936 *)
Lemma J0162 : job_ok 137438953472 91783828983145 1 8409164660925 73107069885858 2 27704399120341.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 73107069885858 2 27704399120341))]. Qed.
