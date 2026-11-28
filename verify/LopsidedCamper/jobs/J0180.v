From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 24739011624960 to 24876450578432 *)
Lemma J0180 : job_ok 137438953472 7705474686322 2 103620074559906 103237530090064 2 8706494749328.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 103237530090064 2 8706494749328))]. Qed.
