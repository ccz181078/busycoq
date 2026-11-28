From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z225 Cuts.b225 Cuts.z226 Cuts.b226 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
