From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 29961691856896 to 30099130810368 *)
Lemma J0218 : job_ok 137438953472 56439341491899 1 78388266764398 114679469044331 1 20766615475911.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 114679469044331 1 20766615475911))]. Qed.
