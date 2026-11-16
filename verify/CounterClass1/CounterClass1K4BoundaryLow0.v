Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Boundary
  BusyCoq.CounterClass1.CounterClass1K4BoundaryShared.
Require Import Lia Compare_dec PeanoNat List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Definition K4Type4Front0 (P:nat->nat->nat->nat->Prop)
    (B:list bool) (H S D:nat) : Prop :=
  H=2*S+D /\
  K4Row P B true (2*H+9) (H+1) /\
  K4Row P B false (2*H+10) (D-2) /\
  P (H+1) 8 (H+1) 12 /\
  P (H+2) 6 (H-1) 16 /\
  P (H+3) 4 H 14 /\
  P (H+4) 2 (H+1) 12 /\
  P (H+5) 0 (D-2) (4*S+18).

Definition K4Type2Front0 (P:nat->nat->nat->nat->Prop)
    (B:list bool) (H S D:nat) : Prop :=
  H=2*S+D /\
  K4Row P B false (2*H+6) (H+3) /\
  P (H+1) 4 (H+1) 8 /\
  P (H+2) 2 (H+2) 6 /\
  P (H+3) 0 D (4*S+10) /\
  K4RowExcept P B true (H-1) (2*H+7) (H+2) /\
  P (H-1) 9 D (4*S+11).

Lemma k4_type4_front0_pre P B H S D:
  K4Type4Front0 P B H S D -> K4Type4PreFront P B H S D.
Proof. intros [? [? [? [? [? [? [? ?]]]]]]]; repeat split; assumption. Qed.

Lemma k4_type2_front0_pre P B H S D:
  K4Type2Front0 P B H S D -> K4Type2PreFront P B H S D.
Proof. intros [? [? [? [? [? [? ?]]]]]]; repeat split; assumption. Qed.

Section Low0.
Variable P:nat->nat->nat->nat->Prop.
Variable C:K4ComplexRules P K4Low0.
Let R:=k4c_simple C.

Lemma k4_low0_end_t2_front B H S D:
  3<=S -> length B=H+1 -> nth 0 B false=false ->
  nth H B false=true -> nth (D+1) B false=true ->
  nth (D+2) B false=true -> nth (D+3) B false=true ->
  K4EndFan P K4T2 B H S D -> K4Type2Front0 P B H S D.
Proof.
  intros HS Hlen B0 BH BD1 BD2 BD3
    [Hhs [RF [Z [RT [EH [EHm ED4]]]]]]. specialize (Z eq_refl).
  destruct RF as [Hrw RF].
  assert (TZ:forall a b, a<length B -> nth a B false=true ->
      a<>H -> a<>H-1 -> 2*a+b=2*H -> P a b 0 (2*H+4)).
  { intros. apply RT; try assumption; intros; assumption. }
  assert (T1:P (D+1) (4*S-2) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (T2:P (D+2) (4*S-4) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (T3:P (D+3) (4*S-6) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (C1:P (H+1) 0 (D+2) (4*S+2)) by
    (applys_eq (k4_inc01 R H (D+2) (4*S-2)); try lia;
      applys_eq EH; lia).
  assert (C2:P (H+2) 0 (D+1) (4*S+6)) by
    (applys_eq (k4_inc01 R (H+1) (D+1) (4*S+2)); try lia;
      applys_eq C1; lia).
  assert (C3:P (H+3) 0 D (4*S+10)) by
    (applys_eq (k4_inc01 R (H+2) D (4*S+6)); try lia;
      applys_eq C2; lia).
  assert (L1:P (D+1) (4*S+1) (H+3) 1).
  { applys_eq (k4_lov2 R (D+1) (4*S-2) 0 (2*H-1)
      0 (2*H-1) (H+1)); try lia;
      [applys_eq T1|applys_eq Z|applys_eq Z]; lia. }
  assert (I1:P (D+1) (4*S+3) (H+2) 5) by
    (applys_eq (k4_inc00_1 R (D+1) (4*S+1) (H+2)); try lia;
      applys_eq L1; lia).
  assert (E2:P (H+2) 2 (H+2) 6).
  { applys_eq (k4_rov R (H+2) 0 (D+1) (4*S+3) (H+2) 5);
      try lia; [applys_eq C2|applys_eq I1]; lia. }
  assert (L2:P (D+2) (4*S-1) (H+3) 1).
  { applys_eq (k4_lov2 R (D+2) (4*S-4) 0 (2*H-1)
      0 (2*H-1) (H+1)); try lia;
      [applys_eq T2|applys_eq Z|applys_eq Z]; lia. }
  assert (Q1:P (H+1) 2 (H+3) 2).
  { applys_eq (k4_rov R (H+1) 0 (D+2) (4*S-1) (H+3) 1);
      try lia; [applys_eq C1|applys_eq L2]; lia. }
  assert (E1:P (H+1) 4 (H+1) 8) by
    (applys_eq (k4_inc00_2 R (H+1) 2 (H+1)); try lia;
      applys_eq Q1; lia).
  assert (LH:P H 3 (H+3) 1).
  { applys_eq (k4c_lov1' C H 0 (D+3) (4*S-6) (H+2));
      try lia; [applys_eq EH|applys_eq T3]; lia. }
  assert (IH:P H 5 (H+2) 5) by
    (applys_eq (k4_inc00_1 R H 3 (H+2)); try lia;
      applys_eq LH; lia).
  assert (TH:P H 7 (H+2) 7).
  { applys_eq (k4_rov R H 5 (H+2) 2 (H+2) 6); try lia;
      [applys_eq IH|applys_eq E2]; lia. }
  assert (LD:P (H-1) 3 (H+2) 1).
  { applys_eq (k4c_lov1' C (H-1) 0 (D+4) (4*S-10) (H+1));
      try lia; [applys_eq (EHm eq_refl)|applys_eq (ED4 eq_refl)]; lia. }
  assert (ID:P (H-1) 5 (H+1) 5) by
    (applys_eq (k4_inc00_1 R (H-1) 3 (H+1)); try lia;
      applys_eq LD; lia).
  assert (QD:P (H-1) 7 (H+3) 3).
  { applys_eq (k4_rov R (H-1) 5 (H+1) 2 (H+3) 2);
      try lia; [applys_eq ID|applys_eq Q1]; lia. }
  assert (Dent:P (H-1) 9 D (4*S+11)).
  { applys_eq (k4_rov R (H-1) 7 (H+3) 0 D (4*S+10));
      try lia; [applys_eq QD|applys_eq C3]; lia. }
  assert (TR:K4RowExcept P B true (H-1) (2*H+7) (H+2)).
  { exists 7. split; try lia. intros a b Hal Han Hab Haw.
    destruct (Nat.eq_dec a H) as [->|HaH]; [applys_eq TH; lia|].
    assert (7<=b) by lia.
    applys_eq (k4_rov R a (b-2) (H+2) 2 (H+2) 6); try lia.
    - applys_eq (k4_inc00_1 R a (b-4) (H+2)); try lia.
      applys_eq (k4_lov2 R a (b-7) 0 (2*H-1)
        0 (2*H-1) (H+1)); try lia.
      + applys_eq (TZ a (b-7)); try assumption; lia.
      + applys_eq Z; lia.
      + applys_eq Z; lia.
    - exact E2. }
  assert (F4:K4ExactRow P B false (2*H+4) (H+4) 0).
  { split; try lia. intros a b Hal Hab Haw.
    assert (a<>H) by (intros ->; congruence).
    assert (5<=b) by lia.
    applys_eq (k4c_lov3 C a (b-5) 0 (2*H-1) H); cbn; try lia.
    - applys_eq (RF a (b-5)); try assumption; lia.
    - applys_eq Z; lia. }
  assert (FR:K4ExactRow P B false (2*H+6) (H+3) 4).
  { split; try lia. intros a b Hal Hab Haw.
    assert (2<=b) by lia.
    applys_eq (k4c_inc00_0 C eq_refl a (b-2) (H+3)); try lia.
    applys_eq (proj2 F4 a (b-2)); try assumption; lia. }
  unfold K4Type2Front0. repeat split; try assumption.
  exists 4. exact FR.
Qed.

Lemma k4_low0_type2_scan_rows B H S D:
  2<=H -> length B=H+1 -> nth H B false=true ->
  2<=D -> D<length B -> D<>H-1 -> nth D B false=true ->
  nth (D-1) B false=true ->
  nth (H-1) B false=true ->
  K4Type2Front0 P B H S D ->
  K4ExactRow P B true (2*H+15) (H-1) 21 /\
  K4ExactRow P B false (2*H+16) (H-1) 22.
Proof.
  intros HH Hlen BH HD HDl HDn BD BDm BHm
    [Hhs [RF0 [E1 [E2 [E3 [RT0 Dent]]]]]].
  destruct RF0 as [df [Hdf RF0]]. destruct RT0 as [dt [Hdt RT0]].
  assert (df=4) by lia. assert (dt=7) by lia. subst df dt.
  assert (A:P (H+2) 4 (H+1) 10) by
    (applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia;
      applys_eq E2; lia).
  assert (TD:P D (4*S+7) (H+2) 7) by
    (apply RT0; assumption || lia).
  assert (Dent':P (H-1) 11 (H+1) 11).
  { applys_eq (k4_rov' R (H-1) 9 D (4*S+7) (H+1) 7);
      try lia; [applys_eq Dent|applys_eq TD]; lia. }
  assert (RT1:K4ExactRow P B true (2*H+9) (H+1) 11).
  { split; try lia. intros a b Hal Hab Haw.
    destruct (Nat.eq_dec a (H-1)) as [->|Han].
    - applys_eq Dent'; lia.
    - assert (2<=b) by lia.
      applys_eq (k4_rov R a (b-2) (H+2) 4 (H+1) 10); try lia.
      + applys_eq (RT0 a (b-2)); try assumption; lia.
      + exact A. }
  assert (B1:P (H+1) 6 H 12) by
    (applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia).
  assert (TH:P H 9 (H+1) 11) by
    (apply (proj2 RT1); assumption || lia).
  assert (B2:P (H+1) 8 (H+1) 12) by
    (applys_eq (k4_rov R (H+1) 6 H 9 (H+1) 11); try lia;
      [applys_eq B1|applys_eq TH]; lia).
  assert (B3:P (H+1) 10 H 16) by
    (applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq B2; lia).
  assert (RF1:K4ExactRow P B false (2*H+8) (D-1) (4*S+14)).
  { applys_eq (k4_exact_row_rov' P R B false (2*H+6)
      (H+3) 0 (D-1) (4*S+10)); try lia.
    - split; assumption.
    - applys_eq E3; lia. }
  assert (TDm:P (D-1) (4*S+11) (H+1) 11) by
    (apply (proj2 RT1); assumption || lia).
  assert (RF2:K4ExactRow P B false (2*H+10) (H+1) 12).
  { applys_eq (k4_exact_row_rov P R B false (2*H+8)
    (D-1) (4*S+11) (H+1) 11); try lia.
    - applys_eq RF1; lia.
    - exact TDm. }
  assert (RT2:K4ExactRow P B true (2*H+11) (H+1) 13) by
    (applys_eq (k4_exact_row_rov P R B true (2*H+9)
      (H+1) 8 (H+1) 12); try lia; assumption).
  assert (Hm13:P (H-1) 13 (H+1) 13) by
    (apply (proj2 RT2); assumption || lia).
  assert (RF3:K4ExactRow P B false (2*H+12) H 16).
  { applys_eq (k4_exact_row_rov' P R B false (2*H+10)
      (H+1) 8 H 12); try lia.
    - applys_eq RF2; lia.
    - applys_eq B2; lia. }
  assert (RT3:K4ExactRow P B true (2*H+13) H 17) by
    (applys_eq (k4_exact_row_rov P R B true (2*H+11)
      (H+1) 10 H 16); try lia; assumption).
  assert (H13:P H 13 H 17) by
    (apply (proj2 RT3); assumption || lia).
  assert (RF4:K4ExactRow P B false (2*H+14) H 18) by
    (applys_eq (k4_exact_row_rov P R B false (2*H+12)
      H 13 H 17); try lia; assumption).
  assert (RT4:K4ExactRow P B true (2*H+15) (H-1) 21).
  { applys_eq (k4_exact_row_rov' P R B true (2*H+13)
      H 13 (H-1) 17); try lia.
    - exact RT3.
    - applys_eq H13; lia. }
  assert (H15:P H 15 (H-1) 21) by
    (apply (proj2 RT4); assumption || lia).
  assert (RF5:K4ExactRow P B false (2*H+16) (H-1) 22) by
    (applys_eq (k4_exact_row_rov P R B false (2*H+14)
      H 15 (H-1) 21); try lia; assumption).
  split; assumption.
Qed.

Lemma k4_low0_end_t4_front B H S D:
  3<=S -> 2<=D -> length B=H+1 ->
  nth 0 B false=true -> nth H B false=true ->
  nth (D-1) B false=true -> nth D B false=true ->
  nth (D+1) B false=true -> nth (D+2) B false=true ->
  nth (D+3) B false=true ->
  K4EndFan P K4T4 B H S D -> K4Type4Front0 P B H S D.
Proof.
  intros HS HD Hlen B0 BH BDm1 BD BD1 BD2 BD3
    [Hhs [RF [Z [RT [EH [_ _]]]]]].
  destruct RF as [Hrw RF].
  assert (TZ:forall a b, a<length B -> nth a B false=true ->
      a<>H -> 2*a+b=2*H -> P a b 0 (2*H+4)).
  { intros. apply RT; try assumption; discriminate. }
  assert (ZT:P 0 (2*H) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (TDm1:P (D-1) (4*S+2) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (TD:P D (4*S) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (TD1:P (D+1) (4*S-2) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (TD2:P (D+2) (4*S-4) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (TD3:P (D+3) (4*S-6) 0 (2*H+4)) by
    (apply TZ; assumption || lia).
  assert (C1:P (H+1) 0 (D+2) (4*S+2)) by
    (applys_eq (k4_inc01 R H (D+2) (4*S-2)); try lia;
      applys_eq EH; lia).
  assert (C2:P (H+2) 0 (D+1) (4*S+6)) by
    (applys_eq (k4_inc01 R (H+1) (D+1) (4*S+2)); try lia;
      applys_eq C1; lia).
  assert (C3:P (H+3) 0 D (4*S+10)) by
    (applys_eq (k4_inc01 R (H+2) D (4*S+6)); try lia;
      applys_eq C2; lia).
  assert (C4:P (H+4) 0 (D-1) (4*S+14)) by
    (applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia;
      applys_eq C3; lia).
  assert (C5:P (H+5) 0 (D-2) (4*S+18)) by
    (applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia;
      applys_eq C4; lia).
  assert (L1:P (D+1) (4*S+1) (H+3) 1).
  { applys_eq (k4c_lov1' C (D+1) (4*S-2) 0 (2*H) (H+2));
      try lia; [applys_eq TD1|applys_eq ZT]; lia. }
  assert (I1:P (D+1) (4*S+3) (H+2) 5) by
    (applys_eq (k4_inc00_1 R (D+1) (4*S+1) (H+2)); try lia;
      applys_eq L1; lia).
  assert (E2:P (H+2) 2 (H+2) 6).
  { applys_eq (k4_rov R (H+2) 0 (D+1) (4*S+3) (H+2) 5);
      try lia; [applys_eq C2|applys_eq I1]; lia. }
  assert (E2':P (H+2) 4 (H+1) 10).
  { applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6);
      try lia; applys_eq E2; lia. }
  assert (L2:P (D+2) (4*S-1) (H+3) 1).
  { applys_eq (k4c_lov1' C (D+2) (4*S-4) 0 (2*H) (H+2));
      try lia; [applys_eq TD2|applys_eq ZT]; lia. }
  assert (Q1:P (H+1) 2 (H+3) 2).
  { applys_eq (k4_rov R (H+1) 0 (D+2) (4*S-1) (H+3) 1);
      try lia; [applys_eq C1|applys_eq L2]; lia. }
  assert (E1:P (H+1) 4 (H+1) 8) by
    (applys_eq (k4_inc00_2 R (H+1) 2 (H+1)); try lia;
      applys_eq Q1; lia).
  assert (E1':P (H+1) 6 H 12) by
    (applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia).
  assert (LH:P H 3 (H+3) 1).
  { applys_eq (k4c_lov1' C H 0 (D+3) (4*S-6) (H+2));
      try lia; [applys_eq EH|applys_eq TD3]; lia. }
  assert (IH:P H 5 (H+2) 5) by
    (applys_eq (k4_inc00_1 R H 3 (H+2)); try lia;
      applys_eq LH; lia).
  assert (QH:P H 7 (H+2) 7).
  { applys_eq (k4_rov R H 5 (H+2) 2 (H+2) 6);
      try lia; [applys_eq IH|applys_eq E2]; lia. }
  assert (TH:P H 9 (H+1) 11).
  { applys_eq (k4_rov R H 7 (H+2) 4 (H+1) 10);
      try lia; [applys_eq QH|applys_eq E2']; lia. }
  assert (X1:P (H+1) 8 (H+1) 12).
  { applys_eq (k4_rov R (H+1) 6 H 9 (H+1) 11);
      try lia; [applys_eq E1'|applys_eq TH]; lia. }
  assert (X2:P (H+2) 6 (H-1) 16).
  { applys_eq (k4_rov' R (H+2) 4 (H+1) 6 (H-1) 12);
      try lia; [applys_eq E2'|applys_eq E1']; lia. }
  assert (L0:P D (4*S+3) (H+3) 1).
  { applys_eq (k4c_lov1' C D (4*S) 0 (2*H) (H+2));
      try lia; [applys_eq TD|applys_eq ZT]; lia. }
  assert (I0:P D (4*S+5) (H+2) 5) by
    (applys_eq (k4_inc00_1 R D (4*S+3) (H+2)); try lia;
      applys_eq L0; lia).
  assert (Q0:P D (4*S+7) (H+2) 7).
  { applys_eq (k4_rov R D (4*S+5) (H+2) 2 (H+2) 6);
      try lia; [applys_eq I0|applys_eq E2]; lia. }
  assert (Q0':P D (4*S+9) (H+1) 11).
  { applys_eq (k4_rov R D (4*S+7) (H+2) 4 (H+1) 10);
      try lia; [applys_eq Q0|applys_eq E2']; lia. }
  assert (X3a:P (H+3) 2 (H+2) 8).
  { applys_eq (k4_rov R (H+3) 0 D (4*S+7) (H+2) 7);
      try lia; [applys_eq C3|applys_eq Q0]; lia. }
  assert (X3:P (H+3) 4 H 14).
  { applys_eq (k4_rov' R (H+3) 2 (H+2) 4 H 10);
      try lia; [applys_eq X3a|applys_eq E2']; lia. }
  assert (Lm1:P (D-1) (4*S+5) (H+3) 1).
  { applys_eq (k4c_lov1' C (D-1) (4*S+2) 0 (2*H) (H+2));
      try lia; [applys_eq TDm1|applys_eq ZT]; lia. }
  assert (Im1:P (D-1) (4*S+7) (H+2) 5) by
    (applys_eq (k4_inc00_1 R (D-1) (4*S+5) (H+2)); try lia;
      applys_eq Lm1; lia).
  assert (Qm1:P (D-1) (4*S+9) (H+2) 7).
  { applys_eq (k4_rov R (D-1) (4*S+7) (H+2) 2 (H+2) 6);
      try lia; [applys_eq Im1|applys_eq E2]; lia. }
  assert (Qm1':P (D-1) (4*S+11) (H+1) 11).
  { applys_eq (k4_rov R (D-1) (4*S+9) (H+2) 4 (H+1) 10);
      try lia; [applys_eq Qm1|applys_eq E2']; lia. }
  assert (X4:P (H+4) 2 (H+1) 12).
  { applys_eq (k4_rov R (H+4) 0 (D-1) (4*S+11) (H+1) 11);
      try lia; [applys_eq C4|applys_eq Qm1']; lia. }
  assert (TR:K4ExactRow P B true (2*H+9) (H+1) 11).
  { split; try lia. intros a b Hal Hab Haw.
    destruct (Nat.eq_dec a H) as [->|Han]; [applys_eq TH; lia|].
    assert (9<=b) by lia.
    assert (TZa:P a (b-9) 0 (2*H+4)) by
      (apply TZ; assumption || lia).
    assert (La:P a (b-6) (H+3) 1).
    { applys_eq (k4c_lov1' C a (b-9) 0 (2*H) (H+2));
        try lia; [applys_eq TZa|applys_eq ZT]; lia. }
    assert (Ia:P a (b-4) (H+2) 5) by
      (applys_eq (k4_inc00_1 R a (b-6) (H+2)); try lia;
        applys_eq La; lia).
    assert (Qa:P a (b-2) (H+2) 7).
    { applys_eq (k4_rov R a (b-4) (H+2) 2 (H+2) 6);
        try lia; [applys_eq Ia|applys_eq E2]; lia. }
    applys_eq (k4_rov R a (b-2) (H+2) 4 (H+1) 10);
      try lia; [applys_eq Qa|applys_eq E2']; lia. }
  assert (F1:K4ExactRow P B false (2*H+1) 0 (2*H+5)).
  { split; try lia. intros a b Hal Hab Haw.
    assert (a<>H) by (intros ->; congruence).
    assert (2<=b) by (rewrite Hlen in Hal; lia).
    applys_eq (k4_rov R a (b-2) 0 (2*H) 0 (2*H+4)); try lia.
    - applys_eq (RF a (b-2)); try assumption; lia.
    - exact ZT. }
  assert (F6:K4ExactRow P B false (2*H+6) (H+5) 0).
  { split; try lia. intros a b Hal Hab Haw.
    assert (5<=b) by lia.
    applys_eq (k4c_lov4 C a (b-5) 0 (2*H) 0 (2*H) (H+2));
      cbn; try lia; [applys_eq (proj2 F1 a (b-5))|applys_eq ZT|applys_eq ZT];
      assumption || lia. }
  assert (F8:K4ExactRow P B false (2*H+8) (H+4) 4).
  { split; try lia. intros a b Hal Hab Haw.
    assert (2<=b) by lia.
    applys_eq (k4c_inc00_0 C eq_refl a (b-2) (H+4)); try lia.
    applys_eq (proj2 F6 a (b-2)); try assumption; lia. }
  assert (FR:K4ExactRow P B false (2*H+10) (D-2) (4*S+18)).
  { applys_eq (k4_exact_row_rov' P R B false (2*H+8)
      (H+4) 0 (D-2) (4*S+14)); try lia.
    - exact F8.
    - applys_eq C4; lia. }
  unfold K4Type4Front0. repeat split; try assumption.
  - exists 11. exact TR.
  - exists (4*S+18). exact FR.
Qed.

Lemma k4_low0_type4_scan_rows B H S D:
  2<=H -> 2<=D -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  nth (D-2) B false=true ->
  K4Type4Front0 P B H S D ->
  K4ExactRow P B true (2*H+17) (H-2) 25 /\
  K4ExactRow P B false (2*H+18) (H-2) 26.
Proof.
  intros HH HD Hlen BH BHm BD2
    [Hhs [RT [RF [E1 [_ [_ [_ _]]]]]]].
  destruct RT as [dt [Hdt RT]]. destruct RF as [df [Hdf RF]].
  assert (dt=11) by lia. assert (df=4*S+18) by lia. subst dt df.
  assert (C10:P (H+1) 10 H 16) by
    (applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq E1; lia).
  assert (RT1:K4ExactRow P B true (2*H+11) (H+1) 13).
  { applys_eq (k4_exact_row_rov P R B true (2*H+9)
      (H+1) 8 (H+1) 12); try lia.
    - split; assumption.
    - exact E1. }
  assert (TD2:P (D-2) (4*S+13) (H+1) 11) by
    (apply RT; assumption || lia).
  assert (TD2':P (D-2) (4*S+15) (H+1) 13) by
    (applys_eq (k4_rov R (D-2) (4*S+13) (H+1) 8 (H+1) 12);
      try lia; assumption).
  assert (RF1:K4ExactRow P B false (2*H+12) (H+1) 14).
  { applys_eq (k4_exact_row_rov P R B false (2*H+10)
      (D-2) (4*S+15) (H+1) 13); try lia.
    - split; try lia. intros a b Hal Hab Haw.
      applys_eq (RF a b Hal Hab Haw); lia.
    - exact TD2'. }
  assert (H11:P H 11 (H+1) 13) by
    (apply (proj2 RT1); try lia; assumption).
  assert (RT2:K4ExactRow P B true (2*H+13) H 17) by
    (applys_eq (k4_exact_row_rov P R B true (2*H+11)
      (H+1) 10 H 16); try lia; assumption).
  assert (H13:P H 13 H 17) by
    (apply (proj2 RT2); try lia; assumption).
  assert (RF2:K4ExactRow P B false (2*H+14) (H-1) 20).
  { applys_eq (k4_exact_row_rov' P R B false (2*H+12)
    (H+1) 10 (H-1) 16); try lia.
    - exact RF1.
    - applys_eq C10; lia. }
  assert (RT3:K4ExactRow P B true (2*H+15) (H-1) 21).
  { applys_eq (k4_exact_row_rov' P R B true (2*H+13)
      H 13 (H-1) 17); try lia.
    - exact RT2.
    - applys_eq H13; lia. }
  assert (Hm17:P (H-1) 17 (H-1) 21) by
    (apply (proj2 RT3); try lia; assumption).
  assert (RF3:K4ExactRow P B false (2*H+16) (H-1) 22).
  { applys_eq (k4_exact_row_rov P R B false (2*H+14)
      (H-1) 17 (H-1) 21); try lia.
    - exact RF2.
    - exact Hm17. }
  assert (RF3':K4Row P B false (2*H+15+1) (H-1)).
  { exists 22. applys_eq RF3; lia. }
  destruct (k4_rows_step P R B (2*H+15) (H-1) (H-1)
    (ex_intro _ 21 RT3) RF3') as [RN1 RN0]; try lia.
  unfold k4_next_x,k4_next_y in RN1,RN0.
  rewrite BHm in RN1,RN0. cbn in RN1,RN0.
  unfold k4_next_x in RN0. rewrite BHm in RN0. cbn in RN0.
  destruct RN1 as [d1 [Hd1 RN1]]. destruct RN0 as [d0 [Hd0 RN0]].
  replace (H-1-1) with (H-2) in Hd1,Hd0,RN1,RN0 by lia.
  assert (d1=25) by lia.
  assert (d0=26) by lia. subst d1 d0.
  split; split; try lia; intros a b Ha Hb Hw.
  - applys_eq (RN1 a b Ha Hb); lia.
  - applys_eq (RN0 a b Ha Hb); lia.
Qed.

Lemma k4_low0_type4_exception B H S D:
  6<=D -> K4Type4Front0 P B H S D ->
  P (H+9) 0 (D-6) (4*S+34).
Proof.
  intros HD [_ [_ [_ [_ [_ [_ [_ HE]]]]]]].
  assert (E1:P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
      applys_eq HE; lia).
  assert (E2:P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
      applys_eq E1; lia).
  assert (E3:P (H+8) 0 (D-5) (4*S+30)) by
    (applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia;
      applys_eq E2; lia).
  applys_eq (k4_inc01 R (H+8) (D-6) (4*S+30)); try lia.
  applys_eq E3; lia.
Qed.

Lemma k4_low0_end_t4_payload B H S D:
  3<=S -> 6<=D -> length B=H+1 ->
  nth 0 B false=true -> nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-5<=z<=D+3 -> nth z B false=true) ->
  K4EndFan P K4T4 B H S D -> K4ScanPayload P K4T4 B H S D.
Proof.
  intros HS HD Hlen B0 BH BHm Hwin HE.
  assert (Hhs:H=2*S+D) by exact (proj1 HE).
  assert (HF:K4Type4Front0 P B H S D).
  { apply (k4_low0_end_t4_front B H S D); try assumption; try lia;
      apply Hwin; lia. }
  destruct (k4_low0_type4_scan_rows B H S D ltac:(lia) ltac:(lia)
    Hlen BH BHm ltac:(apply Hwin; lia) HF) as [RT RF].
  assert (Hpre:K4Type4PreTail P H S D).
  { apply (k4_type4_pretail P R B H S D); try assumption; try lia.
    - intros z Hz. apply Hwin. lia.
    - exact (k4_type4_front0_pre P B H S D HF). }
  assert (Htail:forall j, j<=7 ->
      P (H+8-j) (2+2*j) (H-2) 26).
  { apply (k4_type4_tail P R B H S D); try assumption; try lia;
      apply Hwin; lia. }
  assert (Hex:P (H+9) 0 (D-6) (4*S+34)) by
    (apply (k4_low0_type4_exception B H S D); assumption).
  unfold K4ScanPayload; cbn.
  split; [applys_eq RT; lia|]. split; [applys_eq RF; lia|].
  split; [intros j Hj; applys_eq (Htail j Hj); lia|].
  applys_eq Hex; lia.
Qed.

Lemma k4_low0_type2_exception B H S D:
  5<=D -> K4Type2Front0 P B H S D ->
  P (H+8) 0 (D-5) (4*S+30).
Proof.
  intros HD [_ [_ [_ [_ [HE _]]]]].
  assert (E1:P (H+4) 0 (D-1) (4*S+14)) by
    (applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia;
      applys_eq HE; lia).
  assert (E2:P (H+5) 0 (D-2) (4*S+18)) by
    (applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia;
      applys_eq E1; lia).
  assert (E3:P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
      applys_eq E2; lia).
  assert (E4:P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
      applys_eq E3; lia).
  applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia.
  applys_eq E4; lia.
Qed.

Lemma k4_low0_end_t2_payload B H S D:
  3<=S -> 5<=D -> length B=H+1 ->
  nth 0 B false=false -> nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D+3 -> nth z B false=true) ->
  K4EndFan P K4T2 B H S D -> K4ScanPayload P K4T2 B H S D.
Proof.
  intros HS HD Hlen B0 BH BHm Hwin HE.
  assert (Hhs:H=2*S+D) by exact (proj1 HE).
  assert (HF:K4Type2Front0 P B H S D).
  { apply (k4_low0_end_t2_front B H S D); try assumption;
      apply Hwin; lia. }
  destruct (k4_low0_type2_scan_rows B H S D ltac:(lia) Hlen BH
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply Hwin; lia)
    ltac:(apply Hwin; lia) BHm HF) as [RT RF].
  assert (Hpre:K4Type2PreTail P H S D).
  { apply (k4_type2_pretail P R B H S D); try assumption; try lia.
    - intros z Hz. apply Hwin. lia.
    - exact (k4_type2_front0_pre P B H S D HF). }
  assert (Htail:forall j, j<=6 ->
      P (H+7-j) (2+2*j) (H-1) 22).
  { apply (k4_type2_tail P R B H S D); try assumption; try lia;
      intros z Hz; apply Hwin; lia. }
  assert (Hex:P (H+8) 0 (D-5) (4*S+30)) by
    (apply (k4_low0_type2_exception B H S D); assumption).
  unfold K4ScanPayload; cbn.
  split; [applys_eq RT; lia|]. split; [applys_eq RF; lia|].
  split; [intros j Hj; applys_eq (Htail j Hj); lia|].
  applys_eq Hex; lia.
Qed.

End Low0.
