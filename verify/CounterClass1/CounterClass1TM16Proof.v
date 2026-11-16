Require Import BusyCoq.CounterClass1.CounterClass1_v16 BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K5Common
  BusyCoq.CounterClass1.CounterClass1K5Cycle BusyCoq.CounterClass1.CounterClass1K5FiniteN Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM16.
Open Scope nat.

Definition rules:K5Rules P:={|
  k5_rst01:=PRst01; k5_rst0:=PRst0; k5_inc01:=PInc01;
  k5_rov:=PROv; k5_rov':=PROv';
  k5_lov1:=PLOv1; k5_lov2:=PLOv2; k5_lov2':=PLOv2';
  k5_lov3:=PLOv3; k5_lov3':=PLOv3';
  k5_lov5:=PLOv5; k5_lov4:=PLOv4; k5_lov6:=PLOv6;
  k5_lov7:=PLOv7; k5_lov8:=PLOv8; k5_lov9:=PLOv9
|}.

Definition base_state:K5ScanState:={|
  k5s_kind:=K4T2; k5s_runs:=k5_base_runs; k5s_bits:=k5_base_bits;
  k5s_H:=85; k5s_S:=8; k5s_D:=69; k5s_k:=3
|}.

Lemma base_valid:K5ScanStateValid P base_state.
Proof. exact (k5n_base_start P rules). Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt. intros n.
  set (s:=k5_scan_state_iter n base_state).
  assert (Hs:K5ScanStateValid P s) by
    (unfold s; exact (k5_state_iter_valid P rules base_state base_valid n)).
  assert (Hheight:85+n<=k5s_H s) by
    (unfold s; exact (k5_state_iter_height base_state n)).
  destruct (k5_state_row P s 1 Hs ltac:(lia)) as (b&c&d&HP&Hout).
  eexists _,_; split.
  - apply P0_spec. exact (P0Init b c d HP).
  - split.
    + unfold L2. solve_sigma_score.
    + lia.
Qed.

Print Assumptions nonhalt.
