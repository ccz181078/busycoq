Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles
  BusyCoq.CounterClass1.CounterClass1K4Words.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Definition K4ScanPayload (P: nat -> nat -> nat -> nat -> Prop)
    (kind: K4Kind) (B: list bool) (H S D: nat) : Prop :=
  let g:=k4_gap kind in
  let u:=2*H+2*g+5 in
  let p:=H-g+4 in
  K4ExactRow P B true u p (4*g+1) /\
  K4ExactRow P B false (u+1) p (4*g+2) /\
  (forall j, j<=g+1 -> P (H+g+2-j) (2+2*j) p (4*g+2)) /\
  P (H+g+3) 0 (D-g) (4*S+4*g+10).

Definition K4Type2PreFront (P:nat->nat->nat->nat->Prop)
    (B:list bool) (H S D:nat) : Prop :=
  H=2*S+D /\
  P (H+1) 4 (H+1) 8 /\
  P (H+2) 2 (H+2) 6 /\
  P (H+3) 0 D (4*S+10) /\
  K4RowExcept P B true (H-1) (2*H+7) (H+2) /\
  P (H-1) 9 D (4*S+11).

Definition K4Type4PreFront (P:nat->nat->nat->nat->Prop)
    (B:list bool) (H S D:nat) : Prop :=
  H=2*S+D /\
  K4Row P B true (2*H+9) (H+1) /\
  P (H+1) 8 (H+1) 12 /\
  P (H+2) 6 (H-1) 16 /\
  P (H+3) 4 H 14 /\
  P (H+4) 2 (H+1) 12 /\
  P (H+5) 0 (D-2) (4*S+18).

Lemma k4_type2_front_pre P B H S D:
  K4Type2Front P B H S D -> K4Type2PreFront P B H S D.
Proof. intros [? [? [? [? [? [? ?]]]]]]; repeat split; assumption. Qed.

Lemma k4_type4_front_pre P B H S D:
  K4Type4Front P B H S D -> K4Type4PreFront P B H S D.
Proof. intros [? [? [? [? [? [? [? ?]]]]]]]; repeat split; assumption. Qed.

Lemma k4_scan_start_of_payload P kind runs B H S D k:
  K4RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs -> hd 0 runs=1 ->
  K4HeadBits kind B -> k4_rdrops B (H-k4_gap kind+4)=k ->
  K4ScanPayload P kind B H S D ->
  K4ScanStart P kind runs B H S D k.
Proof.
  intros HS HB Hhead Hbits Hdrop HP.
  unfold K4ScanStart,K4ScanPayload in *. destruct kind; cbn in *.
  - destruct Hbits as [B0 [B1 B2]].
    split; [exact HS|]. split; [exact HB|]. split; [exact Hhead|].
    split; [left; exact B0|]. split; [exact Hdrop|]. exact HP.
  - destruct Hbits as [B0 [B1 B2]].
    split; [exact HS|]. split; [exact HB|]. split; [exact Hhead|].
    split; [right; exact B1|]. split; [exact Hdrop|]. exact HP.
Qed.

Section K4Boundary.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable C: K4ComplexRules P K4Low2.
Let R := k4c_simple C.

Lemma k4_low2_type4_scan_rows B H S D:
  2<=H -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  K4Type4Front P B H S D ->
  K4ExactRow P B true (2*H+17) (H-2) 25 /\
  K4ExactRow P B false (2*H+18) (H-2) 26.
Proof.
  intros HH Hlen BH BHm HF.
  destruct (k4_type4_prefix_start P R B H S D HH Hlen BH BHm HF)
    as [[dt [Hdt RT]] [df [Hdf RF]]].
  assert (dt=25) by lia. assert (df=26) by lia. subst dt df.
  split; split; assumption || lia.
Qed.

Lemma k4_low2_type2_scan_rows B H S D:
  2<=H -> length B=H+1 -> nth H B false=true ->
  D<length B -> D<>H-1 -> nth D B false=true ->
  K4Type2Front P B H S D ->
  K4ExactRow P B true (2*H+15) (H-1) 21 /\
  K4ExactRow P B false (2*H+16) (H-1) 22.
Proof.
  intros HH Hlen BH HDl HDn BD HF.
  destruct (k4_type2_prefix_start P R B H S D HH Hlen BH HDl HDn BD HF)
    as [RT RF].
  assert (RF0: K4Row P B false (2*H+13+1) H) by
    (applys_eq RF; lia).
  destruct (k4_rows_step P R B (2*H+13) H H RT RF0
    ltac:(lia) ltac:(lia) ltac:(intros; lia)
    ltac:(intros E; congruence) ltac:(lia) ltac:(lia) ltac:(lia))
    as [RT' RF'].
  unfold k4_next_x,k4_next_y in RT',RF'. rewrite BH in RT',RF'. cbn in RT',RF'.
    unfold k4_next_x in RF'. rewrite BH in RF'. cbn in RF'.
    destruct RT' as [dt [Hdt RT']].
    destruct RF' as [df [Hdf RF']].
    assert (dt=21) by lia. assert (df=22) by lia. subst dt df.
    split.
    - split; [lia|]. intros a b Hal Hab Haw.
      apply RT'; try assumption; lia.
    - split; [lia|]. intros a b Hal Hab Haw.
      apply RF'; try assumption; lia.
Qed.

Lemma k4_low2_type4_scan_exception B H S D:
  6<=D -> K4Type4Front P B H S D ->
  P (H+9) 0 (D-6) (4*S+34).
Proof.
  intros HD [_ [_ [_ [_ [_ [_ [_ HE]]]]]]].
  assert (E1: P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
     applys_eq HE; lia).
  assert (E2: P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
     applys_eq E1; lia).
  assert (E3: P (H+8) 0 (D-5) (4*S+30)) by
    (applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia;
     applys_eq E2; lia).
  applys_eq (k4_inc01 R (H+8) (D-6) (4*S+30)); try lia.
  applys_eq E3; lia.
Qed.

Lemma k4_low2_type2_scan_exception B H S D:
  5<=D -> K4Type2Front P B H S D ->
  P (H+8) 0 (D-5) (4*S+30).
Proof.
  intros HD [_ [_ [_ [_ [HE _]]]]].
  assert (E1: P (H+4) 0 (D-1) (4*S+14)) by
    (applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia;
     applys_eq HE; lia).
  assert (E2: P (H+5) 0 (D-2) (4*S+18)) by
    (applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia;
     applys_eq E1; lia).
  assert (E3: P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
     applys_eq E2; lia).
  assert (E4: P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
     applys_eq E3; lia).
  applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia.
  applys_eq E4; lia.
Qed.

Definition K4Type2PreTail (P: nat -> nat -> nat -> nat -> Prop)
    (H S D: nat) : Prop :=
  P (H+1) 12 H 18 /\
  P (H+2) 10 (H-1) 20 /\
  P (H+3) 8 (H-1) 20 /\
  P (H+4) 6 H 18 /\
  P (H+5) 4 (H-1) 20 /\
  P (H+6) 2 H 18 /\
  P (H+7) 0 (D-4) (4*S+26).

Lemma k4_low2_type2_pretail B H S D:
  3<=S -> 4<=D -> length B=H+1 -> nth H B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4Type2PreFront P B H S D -> K4Type2PreTail P H S D.
Proof.
  intros HS HD Hlen BH Hbits
    [Hhs [E1 [E2 [E3 [RT0 Dent]]]]].
  destruct RT0 as [dt [Hdt RT0]].
  assert (dt=7) by lia. subst dt.
  assert (T: forall z t, z+t=H -> z<length B -> z<>H-1 ->
      nth z B false=true -> P z (2*t+7) (H+2) 7).
  { intros z t Hzt Hzl Hzn Hzbit. apply RT0; try assumption; lia. }
  assert (A: P (H+2) 4 (H+1) 10).
  { applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia;
      applys_eq E2; lia. }
  assert (B1: P (H+1) 6 H 12).
  { applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia. }
  assert (TH: P H 7 (H+2) 7).
  { exact (T H 0 ltac:(lia) ltac:(rewrite Hlen; lia) ltac:(lia) BH). }
  assert (H9: P H 9 (H+1) 11).
  { eapply (k4_rov R); [exact TH|exact A]. }
  assert (C1: P (H+1) 8 (H+1) 12).
  { eapply (k4_rov R); [exact B1|exact H9]. }
  assert (D1: P (H+1) 10 H 16).
  { eapply (k4_rov' R); [exact C1|applys_eq C1; lia]. }
  assert (H11: P H 11 (H+1) 13).
  { eapply (k4_rov R); [exact H9|exact C1]. }
  assert (H13: P H 13 H 17).
  { eapply (k4_rov R); [exact H11|exact D1]. }
  assert (U: forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+9) (H+1) 11).
  { intros z t HT.
    applys_eq (k4_rov R z (2*t+7) (H+2) 4 (H+1) 10); try lia.
    - exact HT.
    - exact A. }
  assert (V: forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+11) (H+1) 13).
  { intros z t HT.
    applys_eq (k4_rov R z (2*t+9) (H+1) 8 (H+1) 12); try lia.
    - exact (U z t HT).
    - exact C1. }
  assert (W: forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+13) H 17).
  { intros z t HT.
    applys_eq (k4_rov R z (2*t+11) (H+1) 10 H 16); try lia.
    - exact (V z t HT).
    - exact D1. }
  assert (TD: P D (4*S+7) (H+2) 7).
  { replace (4*S+7) with (2*(2*S)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (Dent1: P (H-1) 11 (H+1) 11).
  { applys_eq (k4_rov' R (H-1) 9 D (4*S+7) (H+1) 7); try lia.
    - applys_eq Dent; lia.
    - applys_eq TD; lia. }
  assert (Hm13: P (H-1) 13 (H+1) 13).
  { eapply (k4_rov R); [exact Dent1|exact C1]. }
  assert (Hm15: P (H-1) 15 H 17).
  { eapply (k4_rov R); [exact Hm13|exact D1]. }
  assert (Hm17: P (H-1) 17 (H-1) 21).
  { eapply (k4_rov' R); [exact Hm15|applys_eq H13; lia]. }
  assert (E4: P (H+4) 0 (D-1) (4*S+14)) by
    (applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia;
     applys_eq E3; lia).
  assert (E5: P (H+5) 0 (D-2) (4*S+18)) by
    (applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia;
     applys_eq E4; lia).
  assert (E6: P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
     applys_eq E5; lia).
  assert (E7: P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
     applys_eq E6; lia).
  assert (P1: P (H+1) 12 H 18).
  { eapply (k4_rov R); [exact D1|exact H13]. }
  assert (A6: P (H+2) 6 (H-1) 16).
  { eapply (k4_rov' R); [exact A|applys_eq B1; lia]. }
  assert (A8: P (H+2) 8 (H+1) 14).
  { eapply (k4_rov R); [exact A6|exact Hm13]. }
  assert (P2: P (H+2) 10 (H-1) 20).
  { eapply (k4_rov' R); [exact A8|applys_eq D1; lia]. }
  assert (G32: P (H+3) 2 (H+2) 8).
  { applys_eq (k4_rov R (H+3) 0 D (4*S+7) (H+2) 7); try lia.
    - applys_eq E3; lia.
    - exact TD. }
  assert (G34: P (H+3) 4 H 14).
  { eapply (k4_rov' R); [exact G32|applys_eq A; lia]. }
  assert (G36: P (H+3) 6 (H+1) 14).
  { eapply (k4_rov R); [exact G34|exact H11]. }
  assert (P3: P (H+3) 8 (H-1) 20).
  { eapply (k4_rov' R); [exact G36|applys_eq D1; lia]. }
  assert (TD1: P (D-1) (4*S+9) (H+2) 7).
  { replace (4*S+9) with (2*(2*S+1)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (G42: P (H+4) 2 (H+1) 12).
  { applys_eq (k4_rov R (H+4) 0 (D-1) (4*S+11) (H+1) 11); try lia.
    - applys_eq E4; lia.
    - applys_eq (U (D-1) (2*S+1)); try lia.
      applys_eq TD1; lia. }
  assert (G44: P (H+4) 4 H 16).
  { eapply (k4_rov' R); [exact G42|applys_eq C1; lia]. }
  assert (P4: P (H+4) 6 H 18).
  { eapply (k4_rov R); [exact G44|exact H13]. }
  assert (TD2: P (D-2) (4*S+11) (H+2) 7).
  { replace (4*S+11) with (2*(2*S+2)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (G52: P (H+5) 2 (H+1) 14).
  { applys_eq (k4_rov R (H+5) 0 (D-2) (4*S+15) (H+1) 13); try lia.
    - applys_eq E5; lia.
    - applys_eq (V (D-2) (2*S+2)); try lia.
      applys_eq TD2; lia. }
  assert (P5: P (H+5) 4 (H-1) 20).
  { eapply (k4_rov' R); [exact G52|applys_eq D1; lia]. }
  assert (TD3: P (D-3) (4*S+13) (H+2) 7).
  { replace (4*S+13) with (2*(2*S+3)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (P6: P (H+6) 2 H 18).
  { applys_eq (k4_rov R (H+6) 0 (D-3) (4*S+19) H 17); try lia.
    - applys_eq E6; lia.
    - applys_eq (W (D-3) (2*S+3)); try lia.
      applys_eq TD3; lia. }
  unfold K4Type2PreTail. repeat split; assumption.
Qed.

Lemma k4_low2_type2_tail B H S D:
  H=2*S+D -> 4<=D -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4ExactRow P B true (2*H+15) (H-1) 21 ->
  K4Type2PreTail P H S D ->
  forall j, j<=6 -> P (H+7-j) (2+2*j) (H-1) 22.
Proof.
  intros Hhs HD Hlen BH BHm Hbits [_ RT] Hpre.
  destruct Hpre as [P1 [P2 [P3 [P4 [P5 [P6 P7]]]]]].
  assert (finish: forall a b c d,
      P a b c (3+d) -> c<length B -> nth c B false=true ->
      2*c+d=2*H+15 -> P a (2+b) (H-1) 22).
  { intros a b c d HP Hcl Hcb Hcw.
    applys_eq (k4_rov R a b c d (H-1) 21); try lia.
    - exact HP.
    - apply RT; assumption. }
  intros j Hj.
  assert (j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [->|H] end;
    try subst j; cbn.
  - applys_eq (finish (H+7) 0 (D-4) (4*S+23)); try lia;
      try (applys_eq P7; lia); try (rewrite Hlen; lia);
      try (apply Hbits; lia).
  - applys_eq (finish (H+6) 2 H 15); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+5) 4 (H-1) 17); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+4) 6 H 15); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+3) 8 (H-1) 17); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+2) 10 (H-1) 17); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+1) 12 H 15); try lia; try assumption;
      try (rewrite Hlen; lia).
Qed.

Lemma k4_low2_end_t2_payload B H S D:
  3<=S -> 5<=D -> length B=H+1 ->
  nth 0 B false=false -> nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D+3 -> nth z B false=true) ->
  K4EndFan P K4T2 B H S D -> K4ScanPayload P K4T2 B H S D.
Proof.
  intros HS HD Hlen B0 BH BHm Hwin HE.
  assert (Hhs: H=2*S+D) by exact (proj1 HE).
  assert (HwinD: forall z, D-4<=z<=D -> nth z B false=true).
  { intros z Hz. apply Hwin. lia. }
  assert (HF: K4Type2Front P B H S D).
  { apply (k4_low2_end_t2_front P C); try assumption;
      apply Hwin; lia. }
  destruct (k4_low2_type2_scan_rows B H S D ltac:(lia) Hlen BH
    ltac:(lia) ltac:(lia) ltac:(apply Hwin; lia) HF) as [RT RF].
  assert (Hpre: K4Type2PreTail P H S D).
  { exact (k4_low2_type2_pretail B H S D HS ltac:(lia)
      Hlen BH HwinD (k4_type2_front_pre P B H S D HF)). }
  assert (Htail: forall j, j<=6 ->
      P (H+7-j) (2+2*j) (H-1) 22).
  { exact (k4_low2_type2_tail B H S D Hhs ltac:(lia) Hlen
      BH BHm HwinD RT Hpre). }
  assert (Hex: P (H+8) 0 (D-5) (4*S+30)).
  { apply (k4_low2_type2_scan_exception B H S D); assumption. }
  unfold K4ScanPayload; cbn.
  split; [applys_eq RT; lia|]. split; [applys_eq RF; lia|].
  split; [intros j Hj; applys_eq (Htail j Hj); lia|].
  applys_eq Hex; lia.
Qed.

Definition K4Type4PreTail (P: nat -> nat -> nat -> nat -> Prop)
    (H S D: nat) : Prop :=
  P (H+1) 14 (H-1) 22 /\
  P (H+2) 12 (H-1) 22 /\
  P (H+3) 10 (H-1) 22 /\
  P (H+4) 8 (H-1) 22 /\
  P (H+5) 6 (H-1) 22 /\
  P (H+6) 4 (H-1) 22 /\
  P (H+7) 2 (H-1) 22 /\
  P (H+8) 0 (D-5) (4*S+30).

Lemma k4_low2_type4_pretail B H S D:
  3<=S -> 5<=D -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4Type4PreFront P B H S D -> K4Type4PreTail P H S D.
Proof.
  intros HS HD Hlen BH BHm Hbits
    [Hhs [RT0 [E1 [E2 [E3 [E4 E5]]]]]].
  destruct RT0 as [dt [Hdt RT0]].
  assert (dt=11) by lia. subst dt.
  assert (T: forall z t, z+t=H -> z<length B ->
      nth z B false=true -> P z (2*t+9) (H+1) 11).
  { intros z t Hzt Hzl Hzbit. apply RT0; try assumption; lia. }
  assert (C10: P (H+1) 10 H 16).
  { applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq E1; lia. }
  assert (TH: P H 9 (H+1) 11).
  { exact (T H 0 ltac:(lia) ltac:(rewrite Hlen; lia) BH). }
  assert (THm: P (H-1) 11 (H+1) 11).
  { exact (T (H-1) 1 ltac:(lia) ltac:(rewrite Hlen; lia) BHm). }
  assert (U: forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+11) (H+1) 13).
  { intros z t HT.
    applys_eq (k4_rov R z (2*t+9) (H+1) 8 (H+1) 12); try lia.
    - exact HT.
    - exact E1. }
  assert (V: forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+13) H 17).
  { intros z t HT.
    applys_eq (k4_rov R z (2*t+11) (H+1) 10 H 16); try lia.
    - exact (U z t HT).
    - exact C10. }
  assert (VH: P H 13 H 17).
  { exact (V H 0 TH). }
  assert (W: forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+15) (H-1) 21).
  { intros z t HT.
    applys_eq (k4_rov' R z (2*t+13) H 13 (H-1) 17); try lia.
    - exact (V z t HT).
    - applys_eq VH; lia. }
  assert (H15: P H 15 (H-1) 21).
  { exact (W H 0 TH). }
  assert (Hm17: P (H-1) 17 (H-1) 21).
  { applys_eq (W (H-1) 1 THm); lia. }
  assert (Hm19: P (H-1) 19 (H-2) 25).
  { applys_eq (k4_rov' R (H-1) 17 (H-1) 17 (H-2) 21); try lia.
    - exact Hm17.
    - applys_eq Hm17; lia. }
  assert (C12: P (H+1) 12 H 18).
  { eapply (k4_rov R); [exact C10|exact VH]. }
  assert (P1: P (H+1) 14 (H-1) 22).
  { eapply (k4_rov R); [exact C12|exact H15]. }
  assert (X28: P (H+2) 8 (H+1) 14).
  { eapply (k4_rov R); [exact E2|exact (U (H-1) 1 THm)]. }
  assert (X210: P (H+2) 10 (H-1) 20).
  { eapply (k4_rov' R); [exact X28|applys_eq C10; lia]. }
  assert (P2: P (H+2) 12 (H-1) 22).
  { eapply (k4_rov R); [exact X210|exact Hm17]. }
  assert (X36: P (H+3) 6 (H+1) 14).
  { eapply (k4_rov R); [exact E3|exact (U H 0 TH)]. }
  assert (X38: P (H+3) 8 (H-1) 20).
  { eapply (k4_rov' R); [exact X36|applys_eq C10; lia]. }
  assert (P3: P (H+3) 10 (H-1) 22).
  { eapply (k4_rov R); [exact X38|exact Hm17]. }
  assert (X44: P (H+4) 4 H 16).
  { eapply (k4_rov' R); [exact E4|applys_eq E1; lia]. }
  assert (X46: P (H+4) 6 H 18).
  { eapply (k4_rov R); [exact X44|exact VH]. }
  assert (P4: P (H+4) 8 (H-1) 22).
  { eapply (k4_rov R); [exact X46|exact H15]. }
  assert (TD2: P (D-2) (4*S+13) (H+1) 11).
  { replace (4*S+13) with (2*(2*S+2)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (X52: P (H+5) 2 (H+1) 14).
  { applys_eq (k4_rov R (H+5) 0 (D-2) (4*S+15) (H+1) 13); try lia.
    - applys_eq E5; lia.
    - applys_eq (U (D-2) (2*S+2)); try lia.
      applys_eq TD2; lia. }
  assert (X54: P (H+5) 4 (H-1) 20).
  { eapply (k4_rov' R); [exact X52|applys_eq C10; lia]. }
  assert (P5: P (H+5) 6 (H-1) 22).
  { eapply (k4_rov R); [exact X54|exact Hm17]. }
  assert (E6: P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
     applys_eq E5; lia).
  assert (TD3: P (D-3) (4*S+15) (H+1) 11).
  { replace (4*S+15) with (2*(2*S+3)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (X62: P (H+6) 2 H 18).
  { applys_eq (k4_rov R (H+6) 0 (D-3) (4*S+19) H 17); try lia.
    - applys_eq E6; lia.
    - applys_eq (V (D-3) (2*S+3)); try lia.
      applys_eq TD3; lia. }
  assert (P6: P (H+6) 4 (H-1) 22).
  { eapply (k4_rov R); [exact X62|exact H15]. }
  assert (E7: P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
     applys_eq E6; lia).
  assert (TD4: P (D-4) (4*S+17) (H+1) 11).
  { replace (4*S+17) with (2*(2*S+4)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (P7: P (H+7) 2 (H-1) 22).
  { applys_eq (k4_rov R (H+7) 0 (D-4) (4*S+23) (H-1) 21); try lia.
    - applys_eq E7; lia.
    - applys_eq (W (D-4) (2*S+4)); try lia.
      applys_eq TD4; lia. }
  assert (P8: P (H+8) 0 (D-5) (4*S+30)) by
    (applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia;
     applys_eq E7; lia).
  unfold K4Type4PreTail.
  repeat split; assumption.
Qed.

Lemma k4_low2_type4_tail B H S D:
  H=2*S+D -> 5<=D -> length B=H+1 ->
  nth (H-1) B false=true -> nth (D-5) B false=true ->
  K4ExactRow P B true (2*H+17) (H-2) 25 ->
  K4Type4PreTail P H S D ->
  forall j, j<=7 -> P (H+8-j) (2+2*j) (H-2) 26.
Proof.
  intros Hhs HD Hlen BHm BD [_ RT] Hpre.
  destruct Hpre as [P1 [P2 [P3 [P4 [P5 [P6 [P7 P8]]]]]]].
  assert (finish: forall a b c d,
      P a b c (3+d) -> c<length B -> nth c B false=true ->
      2*c+d=2*H+17 -> P a (2+b) (H-2) 26).
  { intros a b c d HP Hcl Hcb Hcw.
    applys_eq (k4_rov R a b c d (H-2) 25); try lia.
    - exact HP.
    - apply RT; assumption. }
  intros j Hj.
  assert (j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7)
    by lia.
  repeat match goal with H0: _ \/ _ |- _ => destruct H0 as [->|H0] end;
    try subst j; cbn.
  - applys_eq (finish (H+8) 0 (D-5) (4*S+27)); try lia;
      try (applys_eq P8; lia); try (rewrite Hlen; lia); try assumption.
  - applys_eq (finish (H+7) 2 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+6) 4 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+5) 6 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+4) 8 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+3) 10 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+2) 12 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
  - applys_eq (finish (H+1) 14 (H-1) 19); try lia; try assumption;
      try (rewrite Hlen; lia).
Qed.

Lemma k4_low2_end_t4_payload B H S D:
  3<=S -> 6<=D -> length B=H+1 ->
  nth 0 B false=true -> nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-5<=z<=D+3 -> nth z B false=true) ->
  K4EndFan P K4T4 B H S D -> K4ScanPayload P K4T4 B H S D.
Proof.
  intros HS HD Hlen B0 BH BHm Hwin HE.
  assert (Hhs: H=2*S+D) by exact (proj1 HE).
  assert (Hwin4: forall z, D-4<=z<=D -> nth z B false=true).
  { intros z Hz. apply Hwin. lia. }
  assert (HF: K4Type4Front P B H S D).
  { exact (k4_low2_end_t4_front P C B H S D HS ltac:(lia) Hlen B0 BH
      ltac:(apply Hwin; lia) ltac:(apply Hwin; lia)
      ltac:(apply Hwin; lia) ltac:(apply Hwin; lia)
      ltac:(apply Hwin; lia) HE). }
  destruct (k4_low2_type4_scan_rows B H S D ltac:(lia) Hlen BH BHm HF)
    as [RT RF].
  assert (Hpre: K4Type4PreTail P H S D).
  { exact (k4_low2_type4_pretail B H S D HS ltac:(lia) Hlen
      BH BHm Hwin4 (k4_type4_front_pre P B H S D HF)). }
  assert (Htail: forall j, j<=7 ->
      P (H+8-j) (2+2*j) (H-2) 26).
  { exact (k4_low2_type4_tail B H S D Hhs ltac:(lia) Hlen BHm
      ltac:(apply Hwin; lia) RT Hpre). }
  assert (Hex: P (H+9) 0 (D-6) (4*S+34)).
  { apply (k4_low2_type4_scan_exception B H S D); assumption. }
  unfold K4ScanPayload; cbn.
  split; [applys_eq RT; lia|]. split; [applys_eq RF; lia|].
  split; [intros j Hj; applys_eq (Htail j Hj); lia|].
  applys_eq Hex; lia.
Qed.

Lemma k4_low2_t2_true_return B H S D z t:
  z<length B -> nth z B false=true -> z<>H -> z<>H-1 ->
  z+t=H -> K4EndFan P K4T2 B H S D ->
  P z (2*t+3) (H+3) 1 /\ P z (2*t+5) (H+2) 5.
Proof.
  intros Hzl Hzbit HzH HzHm Hzt
    [Hhs [RF [Z [RT [EH [EHm ED]]]]]].
  specialize (Z eq_refl).
  assert (TZ: P z (2*t) 0 (2*H+4)).
  { exact (RT z (2*t) Hzl Hzbit HzH (fun _ => HzHm) ltac:(lia)). }
  assert (LZ: P z (2*t+3) (H+3) 1).
  { applys_eq (k4_lov2 R z (2*t) 0 (2*H-1)
      0 (2*H-1) (H+1)); try lia.
    - applys_eq TZ; lia.
    - applys_eq Z; lia.
    - applys_eq Z; lia. }
  split; [exact LZ|].
  applys_eq (k4_inc00_1 R z (2*t+3) (H+2)); try lia.
  applys_eq LZ; lia.
Qed.

End K4Boundary.
