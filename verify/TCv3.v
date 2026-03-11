From BusyCoq Require Import Individual62.
From BusyCoq Require Import RWLAcc62.

Open Scope list.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition config r :=
to_config 0 0 ([([0; 0; 0; 0], (0%N, 0%N), 1%N); ([1; 0; 0; 0], (0%N, 0%N), 26%N);
           ([1; 0; 0; 1], (0%N, 0%N), 1%N); ([1; 1; 0; 0], (0%N, 0%N), 1%N);
           ([0; 1; 0; 0], (0%N, 0%N), 437%N);
           ([1; 1; 1; 0], (0%N, 0%N), 1%N); ([0; 1; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 400%N);
           ([0; 1; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 390%N);
           ([0; 1; 0; 1], (0%N, 0%N), 1%N);
           ([0; 0; 0; 1], (0%N, 0%N), 390%N);
           ([0; 0; 1; 1], (0%N, 0%N), 1%N);
           ([0; 0; 0; 1], (0%N, 0%N), 389%N);
           ([0; 0; 1; 1], (0%N, 0%N), 1%N);
           ([0; 0; 0; 1], (0%N, 0%N), 389%N);
           ([0; 0; 1; 1], (0%N, 0%N), 1%N)]++r, [], E, R).
Lemma init:
  exists r,
  c0 -->* config r.
Proof.
  unfold config.
  unshelve epose proof (decide_evstep_spec tm 4 320 false 2 6700000 _ _) as I1.
  2: time native_compute; reflexivity.
  eexists.
  apply I1.
Time Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  pose proof init as [r I1].
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_simple.
  clear.
  intros r.
  exists ([([0; 0; 0; 1], (0%N, 0%N), 389%N); ([0; 0; 1; 1], (0%N, 0%N), 1%N)]++r).
  cbn.
  eapply multistep_progress with (n:=1118883).
  eapply multistep_c_spec.
  native_check_eq.
Time Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0RC_0LC0LF_1LD0LE_1RE0LA_0RA0RE_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition config r :=
to_config 0 0 ([([0; 1; 0; 0], (0%N, 0%N), 40%N); ([1; 1; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 435%N);
           ([0; 1; 0; 0], (0%N, 0%N), 400%N);
           ([1; 1; 0; 0], (0%N, 0%N), 1%N);
           ([0; 1; 0; 0], (0%N, 0%N), 390%N);
           ([1; 0; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 390%N);
           ([0; 1; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 389%N);
           ([0; 1; 1; 0], (0%N, 0%N), 1%N);
           ([0; 0; 1; 0], (0%N, 0%N), 389%N);
           ([0; 1; 1; 0], (0%N, 0%N), 1%N)]++r, [], E, R).

Lemma init:
  exists r,
  c0 -->* config r.
Proof.
  unfold config.
  unshelve epose proof (decide_evstep_spec tm 4 320 false 2 6700202 _ _) as I1.
  2: time native_compute; reflexivity.
  eexists.
  apply I1.
Time Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  pose proof init as [r I1].
  eapply multistep_nonhalt.
  1: apply I1.
  eapply progress_nonhalt_simple.
  clear.
  intros r.
  exists ([([0; 0; 1; 0], (0%N, 0%N), 389%N); ([0; 1; 1; 0], (0%N, 0%N), 1%N)]++r).
  cbn.
  eapply multistep_progress with (n:=1118883).
  eapply multistep_c_spec.
  native_check_eq.
Time Qed.

End TM2.

