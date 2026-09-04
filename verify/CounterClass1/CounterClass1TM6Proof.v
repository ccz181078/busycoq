Require Import BusyCoq.CounterClass1.CounterClass1_v6 BusyCoq.CounterClass1.CounterClass1Common Lia.
From BusyCoq Require Import LibTactics Individual62.

Import TM6.
Open Scope nat.

Definition direct_rules: K4DirectRules P := {|
  k4d_simple := {|
    k4_inc01 := PInc01;
    k4_inc1 := PInc1;
    k4_inc00_1 := PInc00_1;
    k4_inc00_2 := PInc00_2;
    k4_rov := PROv;
    k4_rov' := PROv';
    k4_lov1 := PLOv1;
    k4_lov2 := PLOv2
  |};
  k4d_rst0 := PRst0;
  k4d_lov3 := PLOv3
|}.

Lemma p0_base: P0 5 1.
Proof.
  assert (H: P0 0 5) by (apply P0Inc00_1; exact P0Init).
  eapply P0LOv3; [exact H|exact PRst0].
Qed.

Lemma p0_next m:
  2 <= m -> K4Ready P m -> P0 (m+2) 1 -> P0 (2*m+5) 1.
Proof.
  intros Hm [HP [Hpre _]] H0.
  assert (H1: P0 (m+1) 5).
  { apply P0Inc00_1. applys_eq H0; lia. }
  assert (H2: P0 (m-2) 13).
  { applys_eq (P0Ov (m+1) 2 (m-2) 12); try lia.
    - applys_eq H1; lia.
    - applys_eq Hpre; lia. }
  pose proof (k4_p0_sweep P P0 P0Ov' m 2 (m-2)
    ltac:(lia) ltac:(lia) HP H2) as H3.
  applys_eq (P0LOv3 0 (4*m+1) (2*m+1)); try lia.
  - applys_eq H3; lia.
  - applys_eq (proj1 (HP m ltac:(lia)) 0 (2*m)); lia.
Qed.

Fixpoint M (n:nat) :=
  match n with O => 3 | S n => 2*M n+3 end.

Lemma M_bound n: n <= M n /\ 2 <= M n.
Proof. induction n; cbn; lia. Qed.

Lemma loop n: K4Ready P (M n) /\ P0 (M n+2) 1.
Proof.
  induction n as [|n [HR H0]].
  - exact (conj (k4_direct_ready3 P direct_rules) p0_base).
  - cbn. split.
    + apply (k4_direct_ready_next P direct_rules);
        [exact (proj2 (M_bound n))|exact HR].
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
