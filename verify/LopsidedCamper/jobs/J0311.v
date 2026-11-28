From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 42743514529792 to 42880953483264 *)
Lemma J0311 : job_ok 137438953472 113555107867173 1 78790703857544 99525432160559 1 93438855157141.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 99525432160559 1 93438855157141))]. Qed.
