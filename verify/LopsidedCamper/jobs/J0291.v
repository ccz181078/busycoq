From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 39994735460352 to 40132174413824 *)
Lemma J0291 : job_ok 137438953472 87802124593410 2 92174180719604 74246259132251 1 106348521270680.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 74246259132251 1 106348521270680))]. Qed.
