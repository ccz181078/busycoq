Require Import BusyCoq.CounterClass1.CounterClass1_v2 BusyCoq.CounterClass1.CounterClass1Common Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM2.
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
  assert (H1: P 0 5 3 3) by (eapply PLOv3; exact H0).
  assert (H2: P 1 0 0 6) by (eapply PInc1; exact H0).
  assert (H3: P 2 1 4 1) by (eapply PLOv1; exact H2).
  assert (H4: P 3 0 4 2) by (eapply PInc1; exact H3).
  assert (H5: P 0 7 4 3) by (eapply PROv; [exact H1|exact H4]).
  assert (H6: P 4 0 3 6) by (eapply PInc01; exact H4).
  assert (H7: P 0 9 3 7) by (eapply PROv; [exact H5|exact H6]).
  assert (H8: P 3 2 2 8) by (eapply PInc00_2; exact H4).
  assert (H9: P 2 3 3 5) by (eapply PInc00_1; exact H3).
  assert (H10: P 2 5 2 9) by (eapply PROv; [exact H9|exact H8]).
  assert (H11: P 3 4 2 10) by (eapply PROv; [exact H8|exact H10]).
  assert (H12: P 0 11 2 11) by (eapply PROv; [exact H7|exact H11]).
  assert (H13: P 2 7 1 13) by (eapply PROv'; exact H10).
  assert (H14: P 0 13 0 17) by (eapply PROv'; [exact H12|exact H13]).
  assert (H15: P 1 3 4 1) by (eapply PLOv2; exact H2 || exact H0).
  assert (H16: P 1 5 3 5) by (eapply PInc00_1; exact H15).
  assert (H17: P 1 7 2 9) by (eapply PROv; [exact H16|exact H8]).
  assert (H18: P 1 9 1 13) by (eapply PROv'; [exact H17|exact H10]).
  assert (H19: P 1 11 0 17) by (eapply PROv'; exact H18).
  assert (H20: P 2 9 0 17) by (eapply PROv'; [exact H13|exact H18]).
  assert (H21: P 3 6 1 14) by (eapply PROv; [exact H11|exact H13]).
  assert (H22: P 3 8 0 18) by (eapply PROv; [exact H21|exact H19]).
  assert (H23: P 4 2 1 12) by (eapply PROv'; [exact H6|exact H8]).
  assert (H24: P 4 4 1 14) by (eapply PROv; [exact H23|exact H18]).
  assert (H25: P 4 6 0 18) by (eapply PROv; [exact H24|exact H19]).
  assert (H26: P 5 0 2 10) by (eapply PInc01; exact H6).
  assert (H27: P 5 2 1 14) by (eapply PROv; [exact H26|exact H13]).
  assert (H28: P 5 4 0 18) by (eapply PROv; [exact H27|exact H19]).
  assert (H29: P 6 0 1 14) by (eapply PInc01; exact H26).
  assert (H30: P 6 2 0 18) by (eapply PROv; [exact H29|exact H19]).
  assert (H31: P 7 0 0 18) by (eapply PInc01; exact H29).
  unfold K4Ready3BaseFacts; repeat split; assumption.
Qed.

Lemma ready_base: K4Ready3 P 3.
Proof. apply (k4_ready3_base_from_facts P simple_rules), base_facts. Qed.

Lemma left_bridge3 m:
  3 <= m -> K4Phase3 P m ->
  forall a t, a<m -> a+t=2*m -> P a (2*t+5) (2*m+3) 3.
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
  apply (k4_bridge3_to7 P simple_rules m Hm (proj1 HR)).
  apply left_bridge3; [exact Hm|exact (proj1 HR)].
Qed.

Fixpoint M (n:nat) :=
  match n with O => 3 | S n => 2*M n+3 end.

Lemma M_bound n: n+3 <= M n.
Proof. induction n; cbn; lia. Qed.

Lemma loop n: K4Ready3 P (M n).
Proof.
  induction n.
  - exact ready_base.
  - cbn. apply ready_next; [pose proof (M_bound n); lia|exact IHn].
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  destruct (loop n) as [HP _].
  pose proof (proj1 (HP 3 ltac:(pose proof (M_bound n); lia))
    0 (M n+3) ltac:(pose proof (M_bound n); lia) ltac:(lia)) as H.
  eexists _,_; split.
  - apply P0_spec. exact (P0Init _ _ _ H).
  - split.
    + unfold L2; solve_sigma_score.
    + pose proof (M_bound n). lia.
Qed.

Print Assumptions nonhalt.
