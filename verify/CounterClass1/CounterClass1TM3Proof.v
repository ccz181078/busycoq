Require Import BusyCoq.CounterClass1.CounterClass1_v3 BusyCoq.CounterClass1.CounterClass1Common Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM3.
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
  assert (H1: P 0 5 2 5) by (eapply PLOv3; exact H0).
  assert (H2: P 1 0 0 6) by (eapply PInc1; exact H0).
  assert (H3: P 2 1 4 1) by (eapply PLOv1; exact H2).
  assert (H4: P 0 7 3 5) by (eapply PROv'; [exact H1|exact H3]).
  assert (H5: P 3 0 4 2) by (eapply PInc1; exact H3).
  assert (H6: P 3 2 2 8) by (eapply PInc00_2; exact H5).
  assert (H7: P 0 9 2 9) by (eapply PROv; [exact H4|exact H6]).
  assert (H8: P 2 3 3 5) by (eapply PInc00_1; exact H3).
  assert (H9: P 2 5 2 9) by (eapply PROv; [exact H8|exact H6]).
  assert (H10: P 0 11 1 13) by (eapply PROv'; [exact H7|exact H9]).
  assert (H11: P 1 3 4 1) by (eapply PLOv2; exact H2 || exact H0).
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
Proof.
  pose proof base_facts as
    [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [_ _]]]]]]]]]]]].
  split.
  - apply (k4_phase_from_base P simple_rules); try lia.
    + intros a t Ha Hat.
      assert (a=0 \/ a=1 \/ a=2) as Ha' by lia.
      destruct Ha' as [Ha'|[Ha'|Ha']]; subst a.
      * replace t with 5 by lia. exact H0.
      * replace t with 4 by lia. exact H1.
      * replace t with 3 by lia. exact H2.
    + intros k t Hkt.
      assert (k=0 \/ k=1 \/ k=2 \/ k=3) as Hk by lia.
      destruct Hk as [Hk|[Hk|[Hk|Hk]]]; subst k.
      * replace t with 3 by lia. exact H3.
      * replace t with 2 by lia. exact H4.
      * replace t with 1 by lia. exact H5.
      * replace t with 0 by lia. exact H6.
  - unfold K4Prelude; repeat split; assumption.
Qed.

Lemma left_bridge5 m:
  2 <= m -> K4Phase P m ->
  forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+3) 5.
Proof.
  intros Hm HP a t Ha Hat.
  destruct (HP m) as [HO HE]; try lia.
  assert (H: P a (2*t+5) (2*m+2) 5).
  { applys_eq (PLOv3 a (2*t+1) (4*m+1) (2*m+1)); try lia.
    - applys_eq (HO a t); lia.
    - applys_eq (HO 0 (2*m)); lia. }
  applys_eq (PROv' a (2*t+5) (2*m+2) 1 (2*m+3) 1); try lia.
  - exact H.
  - applys_eq (PLOv1 (2*m+1) (2*m+3)); try lia.
    applys_eq (HE (m+1) 0); lia.
Qed.

Lemma ready_next m:
  2 <= m -> K4Ready P m -> K4Ready P (2*m+3).
Proof.
  intros Hm HR.
  apply (k4_ready_next5 P simple_rules m Hm HR).
  apply left_bridge5; [exact Hm|exact (proj1 HR)].
Qed.

Lemma p0_base: P0 2 5.
Proof.
  assert (H: P0 0 5) by (apply P0Inc00_1; apply P0Start; exact P0Init).
  eapply P0LOv3; [exact H|exact PRst0].
Qed.

Lemma p0_next m:
  2 <= m -> K4Ready P m -> P0 (m-1) 5 -> P0 (2*m+2) 5.
Proof.
  intros Hm [HP [_ [Hm2 [Hm1 _]]]] H0.
  assert (H1: P0 m 5).
  { applys_eq (P0Ov' (m-1) 1 m 1); try lia.
    - applys_eq H0; lia.
    - applys_eq Hm1; lia. }
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
  match n with O => 3 | S n => 2*M n+3 end.

Lemma M_bound n: n <= M n /\ 2 <= M n.
Proof. induction n; cbn; lia. Qed.

Lemma loop n: K4Ready P (M n) /\ P0 (M n-1) 5.
Proof.
  induction n as [|n [HR H0]].
  - exact (conj ready3 p0_base).
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
