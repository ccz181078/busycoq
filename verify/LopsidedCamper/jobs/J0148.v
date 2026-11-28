From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 20340965113856 to 20478404067328 *)
Lemma J0148 : job_ok 137438953472 53534525208562 2 37999815180223 47025987561107 1 45126827527290.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 47025987561107 1 45126827527290))]. Qed.
