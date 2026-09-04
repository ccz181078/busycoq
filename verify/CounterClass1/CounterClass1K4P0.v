Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Phase
  BusyCoq.CounterClass1.CounterClass1K4Words.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Record K4P0Rules (P: nat -> nat -> nat -> nat -> Prop)
    (P0: nat -> nat -> Prop) := {
  k4p0_inc00_1: forall a, P0 (1+a) 1 -> P0 a 5;
  k4p0_inc00_2: forall a, P0 (2+a) 2 -> P0 a 8;
  k4p0_ov: forall a b c d,
    P0 a (3+b) -> P a b c d -> P0 c (1+d);
  k4p0_ov': forall a b c d,
    P0 a (4+b) -> P a b (1+c) d -> P0 c (4+d);
  k4p0_lov2: forall a b d n,
    P0 a (5+b) -> P a b 0 (4+d) -> P 0 d 0 (1+n*2) ->
    P0 (2+n) 1;
  k4p0_lov4: forall a b d n,
    P0 a (5+b) -> P a b 0 (4+d) -> P 0 d 0 (n*2) ->
    P0 (2+n) 2
}.

Arguments k4p0_inc00_1 {P P0} _ _ _.
Arguments k4p0_inc00_2 {P P0} _ _ _.
Arguments k4p0_ov {P P0} _ _ _ _ _ _ _.
Arguments k4p0_ov' {P P0} _ _ _ _ _ _ _.
Arguments k4p0_lov2 {P P0} _ _ _ _ _ _ _ _.
Arguments k4p0_lov4 {P P0} _ _ _ _ _ _ _ _.

Section K4P0Scan.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable P0: nat -> nat -> Prop.
Variable R: K4SimpleRules P.
Variable R0: K4P0Rules P P0.

Definition K4P0Follower (u z: nat) : Prop :=
  exists d, 2*z+d=u+5 /\ P0 z d.

Definition K4P0Synced (u z: nat) : Prop :=
  exists d, 2*z+d=u+4 /\ P0 z d.

Lemma k4_p0_follower_step B u x y z:
  K4Row P B true (u+2) (k4_next_x B x y) ->
  K4Row P B false (u+1) y ->
  z < length B ->
  (nth z B false=false -> 0<y) ->
  2*length B<=u+2 ->
  K4P0Follower u z -> K4P0Follower (u+2) (k4_follow B x y z).
Proof.
  intros [dt [Hdt RT]] [df [Hdf RF]] Hzl Hz0 Hlen [d [Hd HP0]].
  destruct (nth z B false) eqn:Hz.
  - exists (1+dt). split.
    + unfold k4_follow. rewrite Hz. cbn. lia.
    + unfold k4_follow. rewrite Hz. cbn.
      applys_eq (k4p0_ov R0 z (d-3) (k4_next_x B x y) dt); try lia.
      * replace (3+(d-3)) with d by lia. exact HP0.
      * apply RT; try assumption; lia.
  - assert (0<y) by (apply Hz0; reflexivity).
    exists (4+df). split.
    + unfold k4_follow. rewrite Hz. cbn. lia.
    + unfold k4_follow. rewrite Hz. cbn.
      applys_eq (k4p0_ov' R0 z (d-4) (y-1) df); try lia.
      * replace (4+(d-4)) with d by lia. exact HP0.
      * replace (1+(y-1)) with y by lia. apply RF; try assumption; lia.
Qed.

Lemma k4_p0_follow_trace B u x y z n:
  K4FollowTrace B u x y z n ->
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  K4P0Follower u z -> K4P0Follower (u+2*n) 0.
Proof.
  intros HT. induction HT; intros RT RF HP0.
  - cbn. applys_eq HP0; lia.
  - destruct (k4_rows_step P R B u x y RT RF H1 H2 H3 H4 H5 H6 H7)
      as [RT' RF'].
    applys_eq (IHHT RT' ltac:(applys_eq RF'; lia)); try lia.
    eapply k4_p0_follower_step; eauto.
Qed.

Lemma k4_p0_synced_step B u x y:
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  x<length B ->
  (nth x B false=true -> 0<x) ->
  2*x<=u ->
  K4P0Synced u x -> K4P0Synced (u+2) (k4_next_x B x y).
Proof.
  intros [dt [Hdt RT]] [df [Hdf RF]] Hxl Hx0 Hxu [d [Hd HP0]].
  destruct (nth x B false) eqn:Hx.
  - assert (0<x) by (apply Hx0; reflexivity).
    exists (4+dt). split.
    + unfold k4_next_x. rewrite Hx. cbn. lia.
    + unfold k4_next_x. rewrite Hx. cbn.
      applys_eq (k4p0_ov' R0 x (d-4) (x-1) dt); try lia.
      * replace (4+(d-4)) with d by lia. exact HP0.
      * replace (1+(x-1)) with x by lia. apply RT; try assumption; lia.
  - exists (1+df). split.
    + unfold k4_next_x. rewrite Hx. cbn. lia.
    + unfold k4_next_x. rewrite Hx. cbn.
      applys_eq (k4p0_ov R0 x (d-3) y df); try lia.
      * replace (3+(d-3)) with d by lia. exact HP0.
      * apply RF; try assumption; lia.
Qed.

Lemma k4_p0_pointer_trace B u x y n:
  K4PointerTrace B u x y n ->
  K4Row P B true u x -> K4Row P B false (u+1) y ->
  K4P0Synced u x -> K4P0Synced (u+2*n) 0.
Proof.
  intros HT. induction HT; intros RT RF HP0.
  - cbn. applys_eq HP0; lia.
  - destruct (k4_rows_step P R B u x y RT RF H H0 H1 H2 H3 H4 H5)
      as [RT' RF'].
    applys_eq (IHHT RT' ltac:(applys_eq RF'; lia)); try lia.
    eapply k4_p0_synced_step; eauto.
Qed.

Lemma k4_p0_scan_t4_reset B H S D k:
  K4ScanData P K4T4 B H S D k -> K4HeadBits K4T4 B ->
  P0 (H-2) 26 ->
  P0 (2*H+k+10) 1.
Proof.
  intros HD HB HP0.
  pose proof HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [RT [RF [Htail Hex]]]]]]]]]].
  cbn [k4_gap] in Hdrop,RT,RF,Htail,Hex.
  destruct (k4_pointer_scan B Hbase (H-2)) as [Hscan _].
  assert (HT: K4PointerTrace B (2*H+17) (H-2) (H-2) (H-2+k)).
  { replace (H-2+k) with (H-2+k4_rdrops B (H-2)) by
      (replace (H-2) with (H-6+4) by lia; rewrite Hdrop; reflexivity).
    apply Hscan; rewrite ?Hlen; lia. }
  assert (HF: K4P0Follower (2*H+17) (H-2)).
  { exists 26. split; assumption || lia. }
  assert (HFT: K4FollowTrace B (2*H+17) (H-2) (H-2)
      (H-2) (H-2+k)).
  { eapply k4_pointer_follow_ok; [exact Hbase|exact HT|].
    unfold K4FollowerOK. left. auto. }
  assert (RT': K4Row P B true (2*H+17) (H-2)).
  { exists 25. applys_eq RT; lia. }
  assert (RF': K4Row P B false (2*H+17+1) (H-2)).
  { exists 26. applys_eq RF; lia. }
  pose proof (k4_p0_follow_trace B _ _ _ _ _
    HFT RT' RF' HF) as HF'.
  assert (HZ: P0 0 (2*(2*H+k+7)+4)).
  { destruct HF' as [d [Hd HP]]. applys_eq HP; lia. }
  pose proof (k4_scan_endfan_t4_data P R B H S D k HD HB) as HE.
  destruct HE as [_ [_ [HZP _]]]. specialize (HZP eq_refl).
  applys_eq (k4p0_lov2 R0 0 (2*(2*H+k+7)-1)
    (2*(2*H+k+7)-1) (2*H+k+8)); try lia.
  - applys_eq HZ; lia.
  - applys_eq HZP; lia.
  - applys_eq HZP; lia.
Qed.

Lemma k4_p0_scan_t2_reset B H S D k:
  K4ScanData P K4T2 B H S D k -> K4HeadBits K4T2 B ->
  P0 (H-1) 21 ->
  P0 (2*H+k+11) 2.
Proof.
  intros HD HB HP0.
  pose proof HD as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [RT [RF [Htail Hex]]]]]]]]]].
  cbn [k4_gap] in Hdrop,RT,RF,Htail,Hex.
  destruct (k4_pointer_scan B Hbase (H-1)) as [Hscan _].
  assert (HT: K4PointerTrace B (2*H+15) (H-1) (H-1) (H-1+k)).
  { replace (H-1+k) with (H-1+k4_rdrops B (H-1)) by
      (replace (H-1) with (H-5+4) by lia; rewrite Hdrop; reflexivity).
    apply Hscan; rewrite ?Hlen; lia. }
  assert (HS0: K4P0Synced (2*H+15) (H-1)).
  { exists 21. split; assumption || lia. }
  assert (RT': K4Row P B true (2*H+15) (H-1)).
  { exists 21. applys_eq RT; lia. }
  assert (RF': K4Row P B false (2*H+15+1) (H-1)).
  { exists 22. applys_eq RF; lia. }
  pose proof (k4_p0_pointer_trace B _ _ _ _ HT
    RT' RF' HS0) as HS0'.
  assert (HPend: P0 0 (2*(2*H+k+7)+3)).
  { destruct HS0' as [d [Hd HP]]. applys_eq HP; lia. }
  pose proof (k4_scan_endfan_t2_data P R B H S D k HD HB) as HE.
  destruct HE as [_ [_ [_ [RTrue _]]]].
  assert (HBp: K4HeadBits K4T4
      (k4_extend B (D+3) (2*S+k+3))).
  { apply (k4_extend_head_bits K4T2); [rewrite Hlen; lia|exact HB]. }
  assert (HT0: P 0 (2*(2*H+k+7)) 0 (2*(2*H+k+7)+4)).
  { apply RTrue; try exact (proj1 HBp); try lia;
      try (rewrite k4_extend_length,Hlen; lia). }
  assert (HPend': P0 0 (2*(2*H+k+7)+5)).
  { replace (2*(2*H+k+7)+5) with (1+(2*(2*H+k+7)+4)) by lia.
    apply (k4p0_ov R0 0 (2*(2*H+k+7)) 0
      (2*(2*H+k+7)+4)); [|exact HT0].
    replace (3+2*(2*H+k+7)) with (2*(2*H+k+7)+3) by lia.
    exact HPend. }
  applys_eq (k4p0_lov4 R0 0 (2*(2*H+k+7))
    (2*(2*H+k+7)) (2*H+k+9)); try lia.
  - applys_eq HPend'; lia.
  - applys_eq HT0; lia.
  - applys_eq HT0; lia.
Qed.

End K4P0Scan.
