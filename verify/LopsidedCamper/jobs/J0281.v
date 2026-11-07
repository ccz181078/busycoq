From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 38620345925632 to 38757784879104 *)
Lemma J0281 : job_ok 137438953472 48021675556435 1 125769875157208 83308863784921 1 91101161633365.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 83308863784921 1 91101161633365))]. Qed.
