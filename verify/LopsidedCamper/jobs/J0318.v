From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43705587204096 to 43843026157568 *)
Lemma J0318 : job_ok 137438953472 136051623858101 1 60623515130031 32828397975213 1 164465215845414.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 32828397975213 1 164465215845414))]. Qed.
