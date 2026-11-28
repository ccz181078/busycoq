From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z62 Cuts.b62 Cuts.z63 Cuts.b63 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
