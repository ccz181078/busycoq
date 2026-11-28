From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 69269232549888 to 69406671503360 *)
Lemma J0504 : job_ok 137438953472 307279153632971 1 4432394280395 280593979825135 1 31736043064789.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 280593979825135 1 31736043064789))]. Qed.
