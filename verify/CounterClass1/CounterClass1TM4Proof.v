Require Import BusyCoq.CounterClass1.CounterClass1_v4 BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Cycle
  BusyCoq.CounterClass1.CounterClass1K4FiniteN BusyCoq.CounterClass1.CounterClass1K4P0 BusyCoq.CounterClass1.CounterClass1K4P0FiniteN
  BusyCoq.CounterClass1.CounterClass1K4P0Low2 Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM4.
Open Scope nat.

Definition simple_rules: K4SimpleRules P := {|
  k4_inc01 := PInc01; k4_inc1 := PInc1;
  k4_inc00_1 := PInc00_1; k4_inc00_2 := PInc00_2;
  k4_rov := PROv; k4_rov' := PROv';
  k4_lov1 := PLOv1; k4_lov2 := PLOv2
|}.

Definition complex_rules: K4ComplexRules P K4Low2.
Proof.
  refine (@Build_K4ComplexRules P K4Low2 simple_rules _ PLOv1' _ _ _).
  - discriminate.
  - cbn. intros. applys_eq (PLOv3 a b c d n); assumption || lia.
  - cbn. intros. applys_eq (PLOv4 a b c d c' d' n); assumption || lia.
  - cbn. intros. applys_eq (PLOv5 a b c d c' d' c'' d'' n);
      assumption || lia.
Defined.

Definition p0_rules: K4P0Rules P P0 := {|
  k4p0_inc00_1 := P0Inc00_1; k4p0_inc00_2 := P0Inc00_2;
  k4p0_ov := P0Ov; k4p0_ov' := P0Ov';
  k4p0_lov2 := P0LOv2; k4p0_lov4 := P0LOv4
|}.

Lemma prebase_data:
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4.
Proof. exact (k4n_low2_prebase_data P complex_rules PRst0). Qed.

Lemma prebase_p0: P0 381 21.
Proof.
  exact (k4n_tm4_prebase_p0_sound P P0 complex_rules p0_rules
    PRst0 P0Init P0Start).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt. intros n.
  destruct (k4_low2_p0_cycle_config P P0 complex_rules p0_rules
    prebase_data prebase_p0 n) as (a&b&HP0&Hscore).
  eexists _,_; split.
  - apply P0_spec. exact HP0.
  - split.
    + unfold L2. solve_sigma_score.
    + pose proof (k4_low2_cycle_height P prebase_data n).
      lia.
Qed.

Print Assumptions nonhalt.
