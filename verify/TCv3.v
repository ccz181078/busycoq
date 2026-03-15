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


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition config '(n,r) :=
to_config 0 0 
         ([([0; 0], (0%N, 0%N), 1%N); ([1; 1], (0%N, 0%N), 1%N);
           ([0; 1], (0%N, 0%N), 1303%N); ([1; 0], (0%N, 0%N), 2%N);
           ([0; 1], (0%N, 0%N), 1%N); ([1; 1], (0%N, 0%N), n)] ++ r,
          [([1; 1], (0%N, 0%N), 983%N); ([1; 0], (0%N, 0%N), 1%N);
           ([1; 1], (0%N, 0%N), 4%N); ([1; 0], (0%N, 0%N), 1%N)], D, R).

Definition r0 :=
           [([1; 0], (0%N, 0%N), 251%N); ([1; 1], (0%N, 0%N), 1%N);
           ([0; 1], (0%N, 0%N), 1%N); ([0; 0], (0%N, 0%N), 1%N);
           ([1; 0], (0%N, 0%N), 8%N); ([1; 1], (0%N, 0%N), 1%N);
           ([0; 1], (0%N, 0%N), 1%N); ([0; 0], (0%N, 0%N), 1%N);
           ([1; 1], (0%N, 0%N), 2%N); ([1; 0], (0%N, 0%N), 381607%N);
           ([1; 1], (0%N, 0%N), 1%N); ([0; 1], (0%N, 0%N), 1%N);
           ([0; 0], (0%N, 0%N), 1%N); ([1; 0], (0%N, 0%N), 127182%N)].


Lemma init:
  c0 -->* config (109290%N,r0).
Proof.
  eapply (decide_evstep_spec tm 2 320 true 2 40000000).
  native_check_eq.
Time Qed.

Opaque N.add.

Lemma BigStep n r:
  config ((n)%N,r) -->+
  config (((1+n))%N,r).
Proof.
  unfold config.
  cbn.
  repeat rewrite Nnat.N2Nat.inj_add.
  eapply multistep_progress with (n:=18030877).
  eapply multistep_c_spec.
  time native_compute.
  rewrite <-const_unfold.
  reflexivity.
Time Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [n r].
  eexists.
  apply BigStep.
Qed.

End TM3.



