From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 18004502904832 to 18141941858304 *)
Lemma J0131 : job_ok 137438953472 11233496443535 1 69786768958801 4403108773827 1 77235631188135.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 4403108773827 1 77235631188135))]. Qed.
