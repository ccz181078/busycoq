From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z221 Cuts.b221 Cuts.z222 Cuts.b222 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
