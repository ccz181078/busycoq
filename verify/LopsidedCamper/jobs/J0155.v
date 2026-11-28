From BusyCoq.LopsidedCamper Require Import Kernel273.
From Coq Require Import Uint63 ZArith.
Open Scope uint63_scope.
(* map steps 21303037788160 to 21440476741632 *)
Lemma J0155 : job_ok 137438953472 49178374257887 1 46685291041485 69092616881618 2 27389523338194.
Proof. split; [vm_compute; reflexivity | native_cast_no_check (eq_refl (Go 69092616881618 2 27389523338194))]. Qed.
