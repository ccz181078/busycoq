From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 35734127902720 to 35871566856192 *)
Lemma J0260 : job_ok 137438953472 24552891356965 1 136250679602022 104011703059120 2 57410343429002.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 104011703059120 2 57410343429002))]. Qed.
