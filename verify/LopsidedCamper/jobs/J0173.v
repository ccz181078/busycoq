From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23776938950656 to 23914377904128 *)
Lemma J0173 : job_ok 137438953472 67484827439762 2 39511393303053 71842363319069 1 35772332811008.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 71842363319069 1 35772332811008))]. Qed.
