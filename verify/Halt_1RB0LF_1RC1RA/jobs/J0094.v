From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z94 Cuts.b94 Cuts.z95 Cuts.b95 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
