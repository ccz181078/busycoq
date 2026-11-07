From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 47416438947840 to 47553877901312 *)
Lemma J0345 : job_ok 137438953472 201145901474248 2 12228072866920 127217967095250 2 86774482181110.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 127217967095250 2 86774482181110))]. Qed.
