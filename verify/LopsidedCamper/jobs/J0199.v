From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 27350351740928 to 27487790694400 *)
Lemma J0199 : job_ok 137438953472 60533961892661 1 62542616698639 1573124754879 1 122121929338067.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 1573124754879 1 122121929338067))]. Qed.
