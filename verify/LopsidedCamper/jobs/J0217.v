From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29824252903424 to 29961691856896 *)
Lemma J0217 : job_ok 137438953472 79706055818195 1 54503077200220 56439341491899 1 78388266764398.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 56439341491899 1 78388266764398))]. Qed.
