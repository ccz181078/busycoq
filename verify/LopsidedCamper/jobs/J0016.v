From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 2199023255552 to 2336462209024 *)
Lemma J0016 : job_ok 137438953472 3615483462207 1 6280121028490 5218702863760 2 5295376862494.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 5218702863760 2 5295376862494))]. Qed.
