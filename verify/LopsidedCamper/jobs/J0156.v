From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21440476741632 to 21577915695104 *)
Lemma J0156 : job_ok 137438953472 69092616881618 2 27389523338194 24778159963346 2 72322456008737.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 24778159963346 2 72322456008737))]. Qed.
