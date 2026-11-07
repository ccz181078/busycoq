From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 50440095924224 to 50577534877696 *)
Lemma J0367 : job_ok 137438953472 62449277073722 2 164531155158450 121175914208889 1 106422993471025.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 121175914208889 1 106422993471025))]. Qed.
