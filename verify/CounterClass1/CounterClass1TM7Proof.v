Require Import BusyCoq.CounterClass1.CounterClass1_v7 BusyCoq.CounterClass1.CounterClass1Common Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM7.
Open Scope nat.

Definition simple_rules: K4SimpleRules P := {|
  k4_inc01 := PInc01; k4_inc1 := PInc1;
  k4_inc00_1 := PInc00_1; k4_inc00_2 := PInc00_2;
  k4_rov := PROv; k4_rov' := PROv';
  k4_lov1 := PLOv1; k4_lov2 := PLOv2
|}.

Lemma base_facts: K4Ready3BaseFacts P.
Proof.
  assert (H0: P 0 1 0 5) by exact PRst0.
  assert (H1: P 0 9 3 7) by (eapply PLOv3; exact H0).
  assert (H2: P 1 0 0 6) by (eapply PInc1; exact H0).
  assert (H3: P 2 1 4 1) by (eapply PLOv1; exact H2).
  assert (H4: P 3 0 4 2) by (eapply PInc1; exact H3).
  assert (H5: P 3 2 2 8) by (eapply PInc00_2; exact H4).
  assert (H6: P 2 3 3 5) by (eapply PInc00_1; exact H3).
  assert (H7: P 2 5 2 9) by (eapply PROv; [exact H6|exact H5]).
  assert (H8: P 3 4 2 10) by (eapply PROv; [exact H5|exact H7]).
  assert (H9: P 0 11 2 11) by (eapply PROv; [exact H1|exact H8]).
  assert (H10: P 2 7 1 13) by (eapply PROv'; exact H7).
  assert (H11: P 0 13 0 17) by (eapply PROv'; [exact H9|exact H10]).
  assert (H12: P 1 3 4 1) by (eapply PLOv2; exact H2 || exact H0).
  assert (H13: P 1 5 3 5) by (eapply PInc00_1; exact H12).
  assert (H14: P 1 7 2 9) by (eapply PROv; [exact H13|exact H5]).
  assert (H15: P 1 9 1 13) by (eapply PROv'; [exact H14|exact H7]).
  assert (H16: P 1 11 0 17) by (eapply PROv'; exact H15).
  assert (H17: P 2 9 0 17) by (eapply PROv'; [exact H10|exact H15]).
  assert (H18: P 3 6 1 14) by (eapply PROv; [exact H8|exact H10]).
  assert (H19: P 3 8 0 18) by (eapply PROv; [exact H18|exact H16]).
  assert (H20: P 4 0 3 6) by (eapply PInc01; exact H4).
  assert (H21: P 4 2 1 12) by (eapply PROv'; [exact H20|exact H5]).
  assert (H22: P 4 4 1 14) by (eapply PROv; [exact H21|exact H15]).
  assert (H23: P 4 6 0 18) by (eapply PROv; [exact H22|exact H16]).
  assert (H24: P 5 0 2 10) by (eapply PInc01; exact H20).
  assert (H25: P 5 2 1 14) by (eapply PROv; [exact H24|exact H10]).
  assert (H26: P 5 4 0 18) by (eapply PROv; [exact H25|exact H16]).
  assert (H27: P 6 0 1 14) by (eapply PInc01; exact H24).
  assert (H28: P 6 2 0 18) by (eapply PROv; [exact H27|exact H16]).
  assert (H29: P 7 0 0 18) by (eapply PInc01; exact H27).
  unfold K4Ready3BaseFacts; repeat split; assumption.
Qed.

Lemma ready_base: K4Ready3 P 3.
Proof. apply (k4_ready3_base_from_facts P simple_rules), base_facts. Qed.

Lemma left_bridge7 m:
  3 <= m -> K4Phase3 P m ->
  forall a t, a<m -> a+t=2*m -> P a (2*t+9) (2*m+3) 7.
Proof.
  intros Hm HP a t Ha Hat.
  destruct (HP m) as [HO _]; try lia.
  applys_eq (PLOv3 a (2*t+1) (4*m+1) (2*m+1)); try lia.
  - applys_eq (HO a t); lia.
  - applys_eq (HO 0 (2*m)); lia.
Qed.

Lemma ready_next m:
  3 <= m -> K4Ready3 P m -> K4Ready3 P (2*m+3).
Proof.
  intros Hm HR.
  apply (k4_ready3_next P simple_rules m Hm HR).
  apply left_bridge7; [exact Hm|exact (proj1 HR)].
Qed.

Lemma p0_base: P0 9 7.
Proof.
  destruct base_facts as [H013 _].
  assert (H10: P 1 0 0 6) by (apply PInc1; exact PRst0).
  assert (H21: P 2 1 4 1) by (apply PLOv1; exact H10).
  assert (H30: P 3 0 4 2) by (apply PInc1; exact H21).
  assert (H32: P 3 2 2 8) by (apply PInc00_2; exact H30).
  assert (H23: P 2 3 3 5) by (apply PInc00_1; exact H21).
  assert (H25: P 2 5 2 9) by (eapply PROv; [exact H23|exact H32]).
  assert (H13: P 1 3 4 1) by (eapply PLOv2; exact H10 || exact PRst0).
  assert (H15: P 1 5 3 5) by (apply PInc00_1; exact H13).
  assert (H17: P 1 7 2 9) by (eapply PROv; [exact H15|exact H32]).
  assert (H19: P 1 9 1 13) by (eapply PROv'; [exact H17|exact H25]).
  pose proof P0Init as Q0.
  assert (Q1: P0 2 9) by (eapply P0Ov'; [exact Q0|exact H23]).
  assert (Q2: P0 1 13) by (eapply P0Ov'; [exact Q1|exact H25]).
  assert (Q3: P0 0 17) by (eapply P0Ov'; [exact Q2|exact H19]).
  eapply P0LOv3; [exact Q3|exact H013].
Qed.

Lemma p0_next m:
  3 <= m -> K4Ready3 P m -> P0 m 7 -> P0 (2*m+3) 7.
Proof.
  intros Hm [HP [Hm4 Hm7]] H0.
  assert (H1: P0 (m-1) 11).
  { applys_eq (P0Ov m 4 (m-1) 10); try lia.
    - exact H0.
    - applys_eq Hm4; lia. }
  assert (H2: P0 (m-3) 17).
  { applys_eq (P0Ov' (m-1) 7 (m-3) 13); try lia.
    - applys_eq H1; lia.
    - applys_eq Hm7; lia. }
  pose proof (k4_p0_sweep3 P P0 P0Ov' m 3 (m-3)
    ltac:(lia) ltac:(lia) HP H2) as H3.
  applys_eq (P0LOv3 0 (4*m+1) (2*m+1)); try lia.
  - applys_eq H3; lia.
  - applys_eq (proj1 (HP m ltac:(lia)) 0 (2*m)); lia.
Qed.

Fixpoint M (n:nat) :=
  match n with O => 9 | S n => 2*M n+3 end.

Lemma M_bound n: n <= M n /\ 3 <= M n.
Proof. induction n; cbn; lia. Qed.

Lemma loop n: K4Ready3 P (M n) /\ P0 (M n) 7.
Proof.
  induction n as [|n [HR H0]].
  - cbn. split.
    + applys_eq (ready_next 3); try lia. exact ready_base.
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
