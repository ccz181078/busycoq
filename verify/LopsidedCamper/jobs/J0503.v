From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69131793596416 to 69269232549888 *)
Lemma J0503 : job_ok 137438953472 199978008770402 2 111115063519043 307279153632971 1 4432394280395.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 307279153632971 1 4432394280395))]. Qed.
