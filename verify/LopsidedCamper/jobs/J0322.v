From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 44255343017984 to 44392781971456 *)
Lemma J0322 : job_ok 137438953472 79156782454896 2 119992256805897 36708547886914 2 163058967738555.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 36708547886914 2 163058967738555))]. Qed.
