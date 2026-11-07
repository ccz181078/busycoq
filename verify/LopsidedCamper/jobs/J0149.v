From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20478404067328 to 20615843020800 *)
Lemma J0149 : job_ok 137438953472 47025987561107 1 45126827527290 3929904546993 1 88841386049912.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 3929904546993 1 88841386049912))]. Qed.
