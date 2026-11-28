From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z135 Cuts.b135 Cuts.z136 Cuts.b136 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
