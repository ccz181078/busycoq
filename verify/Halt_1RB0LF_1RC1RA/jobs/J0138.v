From Coq Require Import Uint63.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import HTop.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Cuts.
Lemma seg : run_seg Cuts.z138 Cuts.b138 Cuts.z139 Cuts.b139 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
