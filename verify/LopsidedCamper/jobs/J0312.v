From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42880953483264 to 43018392436736 *)
Lemma J0312 : job_ok 137438953472 99525432160559 1 93438855157141 72978705028029 1 120604057822412.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 72978705028029 1 120604057822412))]. Qed.
