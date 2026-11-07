From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 51402168598528 to 51539607552000 *)
Lemma J0374 : job_ok 137438953472 696308921219 1 230613451434016 98738836646682 2 133189398700567.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 98738836646682 2 133189398700567))]. Qed.
