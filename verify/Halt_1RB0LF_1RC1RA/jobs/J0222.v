From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z222 Cuts.b222 Cuts.z223 Cuts.b223 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
