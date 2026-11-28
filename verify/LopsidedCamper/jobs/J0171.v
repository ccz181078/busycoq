From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23502061043712 to 23639499997184 *)
Lemma J0171 : job_ok 137438953472 90633769333928 2 15125500936220 1332480205250 2 105045265280365.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1332480205250 2 105045265280365))]. Qed.
