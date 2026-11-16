Require Import BusyCoq.CounterClass1.CounterClass1_v13 BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4CycleLow4
  BusyCoq.CounterClass1.CounterClass1K4FiniteNLow4 Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM13.
Open Scope nat.

Definition simple_rules:K4SimpleRules P:={|
  k4_inc01:=PInc01; k4_inc1:=PInc1;
  k4_inc00_1:=PInc00_1; k4_inc00_2:=PInc00_2;
  k4_rov:=PROv; k4_rov':=PROv';
  k4_lov1:=PLOv1; k4_lov2:=PLOv2
|}.

Definition complex_rules:K4ComplexRules P K4Low4.
Proof.
  refine (@Build_K4ComplexRules P K4Low4 simple_rules _ PLOv1' _ _ _).
  - discriminate.
  - cbn. intros. applys_eq (PLOv3 a b c d n); assumption || lia.
  - cbn. intros. applys_eq (PLOv4 a b c d c' d' n); assumption || lia.
  - cbn. intros. applys_eq (PLOv5 a b c d c' d' c'' d'' n);
      assumption || lia.
Defined.

Lemma prebase_data:
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4.
Proof. exact (k4n_low4_prebase_data P complex_rules PRst0). Qed.

Lemma nonhalt:~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt. intros n.
  destruct (k4_low4_cycle_left_row P complex_rules prebase_data n)
    as (b&c&d&HP&Hout).
  eexists _,_; split.
  - apply P0_spec. exact (P0Init b c d HP).
  - split.
    + unfold L2. solve_sigma_score.
    + pose proof (k4_low4_cycle_height P prebase_data n). lia.
Qed.

Print Assumptions nonhalt.
