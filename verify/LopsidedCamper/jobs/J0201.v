From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27625229647872 to 27762668601344 *)
Lemma J0201 : job_ok 137438953472 100563900937785 1 23749628241611 83790785483707 1 41141218795566.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 83790785483707 1 41141218795566))]. Qed.
