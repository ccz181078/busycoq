From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z277 Cuts.b277 Cuts.z278 Cuts.b278 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
