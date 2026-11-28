From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 49065706389504 to 49203145342976 *)
Lemma J0357 : job_ok 137438953472 211755130810011 1 9040547167722 33595748814905 1 187818404572310.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 33595748814905 1 187818404572310))]. Qed.
