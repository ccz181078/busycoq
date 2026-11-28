From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27487790694400 to 27625229647872 *)
Lemma J0200 : job_ok 137438953472 1573124754879 1 122121929338067 100563900937785 1 23749628241611.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 100563900937785 1 23749628241611))]. Qed.
