From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 60748017434624 to 60885456388096 *)
Lemma J0442 : job_ok 137438953472 170527630943997 1 102838444442138 186619213529093 1 87365336535708.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 186619213529093 1 87365336535708))]. Qed.
