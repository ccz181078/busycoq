From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 43568148250624 to 43705587204096 *)
Lemma J0317 : job_ok 137438953472 122892403444579 1 73164260182788 136051623858101 1 60623515130031.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 136051623858101 1 60623515130031))]. Qed.
