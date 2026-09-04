Require Import BusyCoq.CounterClass1.CounterClass1_v5 BusyCoq.CounterClass1.CounterClass1Common Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM5.
Open Scope nat.

Definition simple_rules: K4SimpleRules P := {|
  k4_inc01 := PInc01; k4_inc1 := PInc1;
  k4_inc00_1 := PInc00_1; k4_inc00_2 := PInc00_2;
  k4_rov := PROv; k4_rov' := PROv';
  k4_lov1 := PLOv1; k4_lov2 := PLOv2
|}.

Lemma base_facts: K4DirectBaseFacts P.
Proof.
  assert (H0: P 0 1 0 5) by exact PRst0.
  assert (H1: P 0 5 4 1) by (eapply PLOv3; exact H0).
  assert (H2: P 0 7 3 5) by (eapply PInc00_1; exact H1).
  assert (H3: P 1 0 0 6) by (eapply PInc1; exact H0).
  assert (H4: P 2 1 4 1) by (eapply PLOv1; exact H3).
  assert (H5: P 3 0 4 2) by (eapply PInc1; exact H4).
  assert (H6: P 3 2 2 8) by (eapply PInc00_2; exact H5).
  assert (H7: P 0 9 2 9) by (eapply PROv; [exact H2|exact H6]).
  assert (H8: P 2 3 3 5) by (eapply PInc00_1; exact H4).
  assert (H9: P 2 5 2 9) by (eapply PROv; [exact H8|exact H6]).
  assert (H10: P 0 11 1 13) by (eapply PROv'; [exact H7|exact H9]).
  assert (H11: P 1 3 4 1) by (eapply PLOv2; exact H3 || exact H0).
  assert (H12: P 1 5 3 5) by (eapply PInc00_1; exact H11).
  assert (H13: P 1 7 2 9) by (eapply PROv; [exact H12|exact H6]).
  assert (H14: P 1 9 1 13) by (eapply PROv'; [exact H13|exact H9]).
  assert (H15: P 2 7 1 13) by (eapply PROv'; exact H9).
  assert (H16: P 3 4 2 10) by (eapply PROv; [exact H6|exact H9]).
  assert (H17: P 3 6 1 14) by (eapply PROv; [exact H16|exact H15]).
  assert (H18: P 4 0 3 6) by (eapply PInc01; exact H5).
  assert (H19: P 4 2 1 12) by (eapply PROv'; [exact H18|exact H6]).
  assert (H20: P 4 4 1 14) by (eapply PROv; [exact H19|exact H14]).
  assert (H21: P 5 0 2 10) by (eapply PInc01; exact H18).
  assert (H22: P 5 2 1 14) by (eapply PROv; [exact H21|exact H15]).
  assert (H23: P 6 0 1 14) by (eapply PInc01; exact H21).
  assert (H24: P 0 13 0 17) by (eapply PROv'; [exact H10|exact H14]).
  unfold K4DirectBaseFacts; repeat split; assumption.
Qed.

Lemma ready3: K4Ready P 3.
Proof. apply (k4_ready3_from_facts P simple_rules), base_facts. Qed.

Lemma left_bridge5 m:
  2 <= m -> K4Phase P m ->
  forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+3) 5.
Proof.
  intros Hm HP a t Ha Hat.
  destruct (HP m) as [HO _]; try lia.
  applys_eq (PInc00_1 a (2*t+5) (2*m+3)); try lia.
  applys_eq (PLOv3 a (2*t+1) (4*m+1) (2*m+1)); try lia.
  - applys_eq (HO a t); lia.
  - applys_eq (HO 0 (2*m)); lia.
Qed.

Lemma ready_next m:
  2 <= m -> K4Ready P m -> K4Ready P (2*m+3).
Proof.
  intros Hm HR.
  apply (k4_ready_next5 P simple_rules m Hm HR).
  apply left_bridge5; [exact Hm|exact (proj1 HR)].
Qed.

Lemma p0_base: P0 10 1.
Proof.
  destruct base_facts as
    [_ [H19 [_ [_ [_ [_ [_ [H42 [_ [_ [_ [_ H013]]]]]]]]]]]].
  assert (H10: P 1 0 0 6) by (apply PInc1; exact PRst0).
  pose proof P0Init as Q0.
  pose proof (P0Start Q0) as Q1.
  assert (Q2: P0 1 5) by (apply P0Inc00_1; exact Q1).
  assert (Q3: P0 5 1).
  { eapply P0End1; [exact Q2|exact H10|exact PRst0|exact PRst0]. }
  assert (Q4: P0 4 5) by (apply P0Inc00_1; exact Q3).
  assert (Q5: P0 1 13) by (eapply P0Ov; [exact Q4|exact H42]).
  assert (Q6: P0 0 17) by (eapply P0Ov'; [exact Q5|exact H19]).
  eapply P0LOv3; [exact Q6|exact H013].
Qed.

Lemma p0_next m:
  2 <= m -> K4Ready P m -> P0 (m+1) 1 -> P0 (2*m+4) 1.
Proof.
  intros Hm [HP [_ [Hm2 [Hm1 _]]]] H0.
  assert (H1: P0 m 5).
  { apply P0Inc00_1. applys_eq H0; lia. }
  assert (H2: P0 (m-1) 9).
  { applys_eq (P0Ov m 2 (m-1) 8); try lia.
    - applys_eq H1; lia.
    - applys_eq Hm2; lia. }
  assert (H3: P (m-1) 5 (m-1) 9).
  { applys_eq (PROv (m-1) 3 m 2 (m-1) 8); try lia.
    - applys_eq (PInc00_1 (m-1) 1 m); try lia.
      applys_eq Hm1; lia.
    - applys_eq Hm2; lia. }
  assert (H4: P0 (m-2) 13).
  { applys_eq (P0Ov' (m-1) 5 (m-2) 9); try lia.
    - applys_eq H2; lia.
    - applys_eq H3; lia. }
  pose proof (k4_p0_sweep P P0 P0Ov' m 2 (m-2)
    ltac:(lia) ltac:(lia) HP H4) as H5.
  applys_eq (P0LOv3 0 (4*m+1) (2*m+1)); try lia.
  - applys_eq H5; lia.
  - applys_eq (proj1 (HP m ltac:(lia)) 0 (2*m)); lia.
Qed.

Fixpoint M (n:nat) :=
  match n with O => 9 | S n => 2*M n+3 end.

Lemma M_bound n: n <= M n /\ 2 <= M n.
Proof. induction n; cbn; lia. Qed.

Lemma loop n: K4Ready P (M n) /\ P0 (M n+1) 1.
Proof.
  induction n as [|n [HR H0]].
  - cbn. split.
    + applys_eq (ready_next 3); try lia. exact ready3.
    + exact p0_base.
  - cbn. split.
    + apply ready_next; [exact (proj2 (M_bound n))|exact HR].
    + applys_eq (p0_next (M n) (proj2 (M_bound n)) HR H0); lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  destruct (loop n) as [_ H0].
  eexists _,_; split.
  - apply P0_spec. exact H0.
  - split.
    + unfold L2; solve_sigma_score.
    + pose proof (M_bound n). lia.
Qed.

Print Assumptions nonhalt.
