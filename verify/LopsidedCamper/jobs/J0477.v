From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 65558380806144 to 65695819759616 *)
Lemma J0477 : job_ok 137438953472 68683935004983 1 226328777988471 114277804874655 1 181353384107575.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 114277804874655 1 181353384107575))]. Qed.
