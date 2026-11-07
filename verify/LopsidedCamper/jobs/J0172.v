From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 23639499997184 to 23776938950656 *)
Lemma J0172 : job_ok 137438953472 1332480205250 2 105045265280365 67484827439762 2 39511393303053.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 67484827439762 2 39511393303053))]. Qed.
