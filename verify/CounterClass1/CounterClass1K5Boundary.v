Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles
  BusyCoq.CounterClass1.CounterClass1K5Common BusyCoq.CounterClass1.CounterClass1K5Phase.
Require Import Lia List Bool Arith.PeanoNat.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Section K5Boundary.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.
Let Q:=K5Q P.
Let C:=k5_q_core_rules P R.

Lemma k5_end_t4_payload B H S D k:
  3<=S -> 12<=D -> length B=H+1 ->
  K4HeadBits K4T4 B -> k4_rdrops B H=k ->
  (forall z, D-5<=z<=D+2 -> nth z B false=true) ->
  (forall z, H+1-S<=z<H+1 -> nth z B false=true) ->
  K5EndFan P K4T4 B H S D -> K5ScanPayload P K4T4 B H S D k.
Proof.
  intros HS HD Hlen Hheads Hdrop Hwin Hlast HE.
  destruct Hheads as [B0 [B1 B2]].
  destruct HE as [Hhs [F0 [Z [TZ [E0 [Edent Hseed]]]]]].
  assert (T:forall a b, a<length B -> nth a B false=true ->
      a<>H -> 2*a+b=2*H -> P a b 0 (2*H+5)).
  { intros a b Hal Hab Han Haw. unfold Q,K5Q in TZ.
    applys_eq (TZ a b Hal Hab Han); try assumption; discriminate || lia. }
  assert (T0:P 0 (2*H) 0 (2*H+5)).
  { apply T; try assumption; lia. }
  assert (E1:P (H+1) 0 (D+1) (4*S+5)).
  { applys_eq (k5_inc01 R H (D+1) (4*S+1)); try lia.
    unfold Q,K5Q in E0. applys_eq E0; lia. }
  assert (E2:P (H+2) 0 D (4*S+9)).
  { applys_eq (k5_inc01 R (H+1) D (4*S+5)); try lia.
    applys_eq E1; lia. }
  assert (E3:P (H+3) 0 (D-1) (4*S+13)).
  { applys_eq (k5_inc01 R (H+2) (D-1) (4*S+9)); try lia.
    applys_eq E2; lia. }
  assert (E4:P (H+4) 0 (D-2) (4*S+17)).
  { applys_eq (k5_inc01 R (H+3) (D-2) (4*S+13)); try lia.
    applys_eq E3; lia. }
  assert (E5:P (H+5) 0 (D-3) (4*S+21)).
  { applys_eq (k5_inc01 R (H+4) (D-3) (4*S+17)); try lia.
    applys_eq E4; lia. }
  assert (E6:P (H+6) 0 (D-4) (4*S+25)).
  { applys_eq (k5_inc01 R (H+5) (D-4) (4*S+21)); try lia.
    applys_eq E5; lia. }
  assert (E7:P (H+7) 0 (D-5) (4*S+29)).
  { applys_eq (k5_inc01 R (H+6) (D-5) (4*S+25)); try lia.
    applys_eq E6; lia. }
  assert (AR:K4ExactRow Q B true (2*H+5) (H+2) 5).
  { split; [lia|]. intros a b Hal Hab Haw.
    unfold Q,K5Q.
    destruct (Nat.eq_dec a H) as [->|Han].
    - assert (TD2:P (D+2) (4*S-4) 0 (2*H+5)).
      { apply T; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
      applys_eq (@k5_lov2' P R H 0 (D+2) (4*S-4) (H+2)
        ltac:(unfold Q,K5Q in E0; applys_eq E0; lia)
        ltac:(applys_eq TD2; lia)); lia.
    - assert (5<=b) by lia.
      applys_eq (@k5_lov2' P R a (b-5) 0 (2*H) (H+2)
        ltac:(applys_eq (T a (b-5)); try assumption; lia)
        ltac:(applys_eq T0; lia)); lia. }
  assert (Arow:forall a b, a<length B -> nth a B false=true ->
      2*a+b=2*H+5 -> P a b (H+2) 6).
  { intros a b Hal Hab Haw. unfold Q,K5Q in AR.
    exact (proj2 AR a b Hal Hab Haw). }
  assert (N5:P H 5 (H+2) 6).
  { apply Arow; [lia|apply Hlast; lia|lia]. }
  assert (G2:P (H+2) 2 (H+2) 7).
  { applys_eq (k5_rov R (H+2) 0 D (4*S+5) (H+2) 6); try lia.
    - applys_eq E2; lia.
    - apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia]. }
  assert (G4:P (H+2) 4 (H+1) 11).
  { applys_eq (k5_rov' R (H+2) 2 (H+2) 2 (H+1) 7);
      try lia; applys_eq G2; lia. }
  assert (L4:P (H+1) 4 (H+1) 9).
  { assert (TD1:P (D+1) (4*S-2) 0 (2*H+5)).
    { apply T; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
    applys_eq (@k5_lov3' P R (H+1) 0 (D+1) (4*S-2)
      0 (2*H) (H+1) ltac:(applys_eq E1; lia)
      ltac:(applys_eq TD1; lia) ltac:(applys_eq T0; lia)); lia. }
  assert (L6:P (H+1) 6 H 13).
  { applys_eq (k5_rov' R (H+1) 4 (H+1) 4 H 9);
      try lia; applys_eq L4; lia. }
  assert (N7:P H 7 (H+2) 8).
  { applys_eq (k5_rov R H 5 (H+2) 2 (H+2) 7); try lia;
      assumption. }
  assert (N9:P H 9 (H+1) 12).
  { applys_eq (k5_rov R H 7 (H+2) 4 (H+1) 11); try lia;
      assumption. }
  assert (L8:P (H+1) 8 (H+1) 13).
  { applys_eq (k5_rov R (H+1) 6 H 9 (H+1) 12); try lia;
      assumption. }
  assert (N11:P H 11 (H+1) 14).
  { applys_eq (k5_rov R H 9 (H+1) 8 (H+1) 13); try lia;
      assumption. }
  assert (L10:P (H+1) 10 H 17).
  { applys_eq (k5_rov' R (H+1) 8 (H+1) 8 H 13);
      try lia; applys_eq L8; lia. }
  assert (N13:P H 13 H 18).
  { applys_eq (k5_rov R H 11 (H+1) 10 H 17); try lia;
      assumption. }
  assert (chain:forall a b, P a b (H+2) 6 ->
      P a (b+2) (H+2) 8 /\ P a (b+4) (H+1) 12 /\
      P a (b+6) (H+1) 14 /\ P a (b+8) H 18).
  { intros a b HA.
    assert (C2:P a (b+2) (H+2) 8) by
      (applys_eq (k5_rov R a b (H+2) 2 (H+2) 7); try lia; assumption).
    assert (C4:P a (b+4) (H+1) 12) by
      (applys_eq (k5_rov R a (b+2) (H+2) 4 (H+1) 11);
        try lia; assumption).
    assert (C6:P a (b+6) (H+1) 14) by
      (applys_eq (k5_rov R a (b+4) (H+1) 8 (H+1) 13);
        try lia; assumption).
    assert (C8:P a (b+8) H 18) by
      (applys_eq (k5_rov R a (b+6) (H+1) 10 H 17);
        try lia; assumption).
    repeat split; assumption. }
  assert (BR:K4ExactRow Q B true (2*H+7) (H+2) 7).
  { assert (G2Q:Q (H+2) 2 (H+2) 6) by
      (unfold Q,K5Q; applys_eq G2; lia).
    applys_eq (k4_exact_row_rov Q C B true (2*H+5) (H+2) 2
      (H+2) 6 ltac:(lia) AR G2Q ltac:(lia)); lia. }
  assert (CR:K4ExactRow Q B true (2*H+9) (H+1) 11).
  { assert (G4Q:Q (H+2) 4 (H+1) 10) by
      (unfold Q,K5Q; applys_eq G4; lia).
    applys_eq (k4_exact_row_rov Q C B true (2*H+7) (H+2) 4
      (H+1) 10 ltac:(lia) BR G4Q ltac:(lia)); lia. }
  assert (DR:K4ExactRow Q B true (2*H+11) (H+1) 13).
  { assert (L8Q:Q (H+1) 8 (H+1) 12) by
      (unfold Q,K5Q; applys_eq L8; lia).
    applys_eq (k4_exact_row_rov Q C B true (2*H+9) (H+1) 8
      (H+1) 12 ltac:(lia) CR L8Q ltac:(lia)); lia. }
  assert (RT:K4ExactRow Q B true (2*H+13) H 17).
  { assert (L10Q:Q (H+1) 10 H 16) by
      (unfold Q,K5Q; applys_eq L10; lia).
    applys_eq (k4_exact_row_rov Q C B true (2*H+11) (H+1) 10
      H 16 ltac:(lia) DR L10Q ltac:(lia)); lia. }
  assert (T0Q:Q 0 (2*H) 0 (2*H+4)) by
    (unfold Q,K5Q; applys_eq T0; lia).
  assert (F1:K4ExactRow Q B false (2*H+1) 0 (2*H+5)).
  { split; [lia|]. intros a b Hal Hab Haw.
    assert (Ha:a<H+1-S).
    { destruct (Nat.lt_ge_cases a (H+1-S)); [assumption|].
      assert (nth a B false=true) by (apply Hlast; lia). congruence. }
    assert (2<=b) by lia.
    unfold Q,K5Q.
    applys_eq (k5_rov R a (b-2) 0 (2*H) 0 (2*H+5)); try lia.
    - unfold Q,K5Q in F0. applys_eq (proj2 F0 a (b-2) Hal Hab); lia.
    - exact T0. }
  assert (F8:K4ExactRow Q B false (2*H+8) (H+4) 4).
  { split; [lia|]. intros a b Hal Hab Haw. unfold Q,K5Q.
    assert (7<=b) by lia.
    assert (HA:P a (b-7) 0 (2*H+6)).
    { unfold Q,K5Q in F1. applys_eq (proj2 F1 a (b-7) Hal Hab); lia. }
    applys_eq (@k5_lov6 P R a (b-7) 0 (2*H) 0 (2*H) (H+2)
      ltac:(applys_eq HA; lia) ltac:(applys_eq T0; lia)
      ltac:(applys_eq T0; lia)); lia. }
  assert (E4Q:Q (H+4) 0 (1+(D-3)) (4*S+16)) by
    (unfold Q,K5Q; applys_eq E4; lia).
  assert (F10:K4ExactRow Q B false (2*H+10) (D-3) (4*S+20)).
  { applys_eq (k4_exact_row_rov' Q C B false (2*H+8) (H+4) 0
      (D-3) (4*S+16) ltac:(lia) F8 E4Q ltac:(lia)); lia. }
  assert (TD3:P (D-3) (4*S+11) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia]. }
  destruct (chain (D-3) (4*S+11) TD3) as [TD32 [TD34 [TD36 TD38]]].
  assert (TD36Q:Q (D-3) (4*S+17) (H+1) 13) by
    (unfold Q,K5Q; applys_eq TD36; lia).
  assert (F12:K4ExactRow Q B false (2*H+12) (H+1) 14).
  { applys_eq (k4_exact_row_rov Q C B false (2*H+10) (D-3)
      (4*S+17) (H+1) 13 ltac:(lia)
      ltac:(applys_eq F10; lia) TD36Q ltac:(lia)); lia. }
  assert (L10Q:Q (H+1) 10 (1+(H-1)) 16) by
    (unfold Q,K5Q; applys_eq L10; lia).
  assert (RF:K4ExactRow Q B false (2*H+14) (H-1) 20).
  { applys_eq (k4_exact_row_rov' Q C B false (2*H+12) (H+1) 10
      (H-1) 16 ltac:(lia) F12 L10Q ltac:(lia)); lia. }
  assert (P1:P (H+1) 12 H 19).
  { applys_eq (k5_rov R (H+1) 10 H 13 H 18); try lia;
      [applys_eq L10|applys_eq N13]; lia. }
  assert (Hm1:P (H-1) 7 (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hlast; lia|lia]. }
  destruct (chain (H-1) 7 Hm1) as [Hm9 [Hm11 [Hm13 Hm15]]].
  assert (P26:P (H+2) 6 (H-1) 17).
  { applys_eq (k5_rov' R (H+2) 4 (H+1) 6 (H-1) 13);
      try lia; [applys_eq G4|applys_eq L6]; lia. }
  assert (P28:P (H+2) 8 (H+1) 15).
  { applys_eq (k5_rov R (H+2) 6 (H-1) 13 (H+1) 14);
      try lia; [applys_eq P26|applys_eq Hm13]; lia. }
  assert (P2:P (H+2) 10 (H-1) 21).
  { applys_eq (k5_rov' R (H+2) 8 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P28|applys_eq L10]; lia. }
  assert (TD1:P (D-1) (4*S+7) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia]. }
  destruct (chain (D-1) (4*S+7) TD1) as [TD12 [TD14 [TD16 TD18]]].
  assert (P32:P (H+3) 2 (H+2) 9).
  { applys_eq (k5_rov R (H+3) 0 (D-1) (4*S+9) (H+2) 8);
      try lia; [applys_eq E3|applys_eq TD12]; lia. }
  assert (P34:P (H+3) 4 H 15).
  { applys_eq (k5_rov' R (H+3) 2 (H+2) 4 H 11);
      try lia; [applys_eq P32|applys_eq G4]; lia. }
  assert (P36:P (H+3) 6 (H+1) 15).
  { applys_eq (k5_rov R (H+3) 4 H 11 (H+1) 14);
      try lia; [applys_eq P34|applys_eq N11]; lia. }
  assert (P3:P (H+3) 8 (H-1) 21).
  { applys_eq (k5_rov' R (H+3) 6 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P36|applys_eq L10]; lia. }
  assert (TD2:P (D-2) (4*S+9) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia]. }
  destruct (chain (D-2) (4*S+9) TD2) as [TD22 [TD24 [TD26 TD28]]].
  assert (P42:P (H+4) 2 (H+1) 13).
  { applys_eq (k5_rov R (H+4) 0 (D-2) (4*S+13) (H+1) 12);
      try lia; [applys_eq E4|applys_eq TD24]; lia. }
  assert (P44:P (H+4) 4 H 17).
  { applys_eq (k5_rov' R (H+4) 2 (H+1) 8 H 13);
      try lia; [applys_eq P42|applys_eq L8]; lia. }
  assert (P4:P (H+4) 6 H 19).
  { applys_eq (k5_rov R (H+4) 4 H 13 H 18); try lia;
      [applys_eq P44|applys_eq N13]; lia. }
  assert (P52:P (H+5) 2 (H+1) 15).
  { applys_eq (k5_rov R (H+5) 0 (D-3) (4*S+17) (H+1) 14);
      try lia; [applys_eq E5|applys_eq TD36]; lia. }
  assert (P5:P (H+5) 4 (H-1) 21).
  { applys_eq (k5_rov' R (H+5) 2 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P52|applys_eq L10]; lia. }
  assert (TD4:P (D-4) (4*S+13) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia]. }
  destruct (chain (D-4) (4*S+13) TD4) as [TD42 [TD44 [TD46 TD48]]].
  assert (P6:P (H+6) 2 H 19).
  { applys_eq (k5_rov R (H+6) 0 (D-4) (4*S+21) H 18);
      try lia; [applys_eq E6|applys_eq TD48]; lia. }
  unfold K5ScanPayload.
  split; [exact (conj B0 (conj B1 B2))|].
  split; [exact Hdrop|].
  split; [exact RT|].
  split; [exact RF|].
  split; [|exact E7].
  unfold K5Tail. repeat split; assumption.
Qed.

Lemma k5_end_t2_payload B H S D k:
  3<=S -> 12<=D -> length B=H+1 ->
  K4HeadBits K4T2 B -> k4_rdrops B H=k ->
  (forall z, D-5<=z<=D+2 -> nth z B false=true) ->
  (forall z, H+1-S<=z<H+1 -> nth z B false=true) ->
  K5EndFan P K4T2 B H S D -> K5ScanPayload P K4T2 B H S D k.
Proof.
  intros HS HD Hlen Hheads Hdrop Hwin Hlast HE.
  destruct Hheads as [B0 [B1 B2]].
  destruct HE as [Hhs [F0 [Z [TZ [E0 [Edent Hseed]]]]]].
  specialize (Z eq_refl). specialize (Edent eq_refl).
  specialize (Hseed eq_refl). unfold Q,K5Q in Z,E0,Edent,Hseed.
  assert (T:forall a b, a<length B -> nth a B false=true ->
      a<>H -> a<>H-1 -> 2*a+b=2*H -> P a b 0 (2*H+5)).
  { intros a b Hal Hab HaH HaHm Haw.
    applys_eq (TZ a b Hal Hab HaH ltac:(intros _; exact HaHm) Haw); lia. }
  assert (E1:P (H+1) 0 (D+1) (4*S+5)).
  { applys_eq (k5_inc01 R H (D+1) (4*S+1)); try lia.
    applys_eq E0; lia. }
  assert (E2:P (H+2) 0 D (4*S+9)).
  { applys_eq (k5_inc01 R (H+1) D (4*S+5)); try lia.
    applys_eq E1; lia. }
  assert (E3:P (H+3) 0 (D-1) (4*S+13)).
  { applys_eq (k5_inc01 R (H+2) (D-1) (4*S+9)); try lia.
    applys_eq E2; lia. }
  assert (E4:P (H+4) 0 (D-2) (4*S+17)).
  { applys_eq (k5_inc01 R (H+3) (D-2) (4*S+13)); try lia.
    applys_eq E3; lia. }
  assert (E5:P (H+5) 0 (D-3) (4*S+21)).
  { applys_eq (k5_inc01 R (H+4) (D-3) (4*S+17)); try lia.
    applys_eq E4; lia. }
  assert (E6:P (H+6) 0 (D-4) (4*S+25)).
  { applys_eq (k5_inc01 R (H+5) (D-4) (4*S+21)); try lia.
    applys_eq E5; lia. }
  assert (E7:P (H+7) 0 (D-5) (4*S+29)).
  { applys_eq (k5_inc01 R (H+6) (D-5) (4*S+25)); try lia.
    applys_eq E6; lia. }
  assert (Arow:forall a b, a<length B -> nth a B false=true ->
      a<>H-1 -> 2*a+b=2*H+5 -> P a b (H+2) 6).
  { intros a b Hal Hab HaHm Haw.
    destruct (Nat.eq_dec a H) as [->|HaH].
    - assert (TD2:P (D+2) (4*S-4) 0 (2*H+5)).
      { apply T; [rewrite Hlen; lia|apply Hwin; lia|lia|lia|lia]. }
      applys_eq (@k5_lov2' P R H 0 (D+2) (4*S-4) (H+2)
        ltac:(applys_eq E0; lia) ltac:(applys_eq TD2; lia)); lia.
    - assert (5<=b) by lia.
      applys_eq (@k5_lov4 P R a (b-5) 0 (2*H-1) 0 (2*H-1)
        (H+2) ltac:(applys_eq (T a (b-5)); try assumption; lia)
        ltac:(applys_eq Z; lia) ltac:(applys_eq Z; lia)); lia. }
  assert (N5:P H 5 (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hlast; lia|lia|lia]. }
  assert (TD0:P D (4*S) 0 (2*H+5)).
  { apply T; [rewrite Hlen; lia|apply Hwin; lia|lia|lia|lia]. }
  assert (AD:P D (4*S+5) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
  assert (G2:P (H+2) 2 (H+2) 7).
  { applys_eq (k5_rov R (H+2) 0 D (4*S+5) (H+2) 6); try lia;
      [applys_eq E2|applys_eq AD]; lia. }
  assert (G4:P (H+2) 4 (H+1) 11).
  { applys_eq (k5_rov' R (H+2) 2 (H+2) 2 (H+1) 7);
      try lia; applys_eq G2; lia. }
  assert (TD1:P (D+1) (4*S-2) 0 (2*H+5)).
  { apply T; [rewrite Hlen; lia|apply Hwin; lia|lia|lia|lia]. }
  assert (L4:P (H+1) 4 (H+1) 9).
  { applys_eq (@k5_lov8 P R (H+1) 0 (D+1) (4*S-2)
      0 (2*H-1) 0 (2*H-1) (H+1)
      ltac:(applys_eq E1; lia) ltac:(applys_eq TD1; lia)
      ltac:(applys_eq Z; lia) ltac:(applys_eq Z; lia)); lia. }
  assert (L6:P (H+1) 6 H 13).
  { applys_eq (k5_rov' R (H+1) 4 (H+1) 4 H 9);
      try lia; applys_eq L4; lia. }
  assert (N7:P H 7 (H+2) 8).
  { applys_eq (k5_rov R H 5 (H+2) 2 (H+2) 7); try lia;
      [applys_eq N5|applys_eq G2]; lia. }
  assert (N9:P H 9 (H+1) 12).
  { applys_eq (k5_rov R H 7 (H+2) 4 (H+1) 11); try lia;
      [applys_eq N7|applys_eq G4]; lia. }
  assert (L8:P (H+1) 8 (H+1) 13).
  { applys_eq (k5_rov R (H+1) 6 H 9 (H+1) 12); try lia;
      [applys_eq L6|applys_eq N9]; lia. }
  assert (N11:P H 11 (H+1) 14).
  { applys_eq (k5_rov R H 9 (H+1) 8 (H+1) 13); try lia;
      [applys_eq N9|applys_eq L8]; lia. }
  assert (L10:P (H+1) 10 H 17).
  { applys_eq (k5_rov' R (H+1) 8 (H+1) 8 H 13);
      try lia; applys_eq L8; lia. }
  assert (N13:P H 13 H 18).
  { applys_eq (k5_rov R H 11 (H+1) 10 H 17); try lia;
      [applys_eq N11|applys_eq L10]; lia. }
  assert (S5:P (H-1) 5 (H+1) 6).
  { applys_eq (@k5_lov2' P R (H-1) 0 (D+3) (4*S-8) (H+1)
      ltac:(applys_eq Edent; lia) ltac:(applys_eq Hseed; lia)); lia. }
  assert (S9:P (H-1) 9 (D-1) (4*S+14)).
  { applys_eq (@k5_lov9 P R (H-1) 5 (H+1) 0 (D+1) (4*S-2)
      0 (2*H-1) 0 (2*H-1) (H+2) (D-1) (4*S+13)
      ltac:(applys_eq S5; lia) ltac:(applys_eq E1; lia)
      ltac:(applys_eq TD1; lia) ltac:(applys_eq Z; lia)
      ltac:(applys_eq Z; lia) ltac:(applys_eq E3; lia)); lia. }
  assert (AD1:P (D-1) (4*S+7) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
  assert (AD1':P (D-1) (4*S+9) (H+2) 8).
  { applys_eq (k5_rov R (D-1) (4*S+7) (H+2) 2 (H+2) 7);
      try lia; [applys_eq AD1|applys_eq G2]; lia. }
  assert (S11:P (H-1) 11 (H+1) 12).
  { applys_eq (k5_rov' R (H-1) 9 (D-1) (4*S+9) (H+1) 8);
      try lia; [applys_eq S9|applys_eq AD1']; lia. }
  assert (S13:P (H-1) 13 (H+1) 14).
  { applys_eq (k5_rov R (H-1) 11 (H+1) 8 (H+1) 13);
      try lia; [applys_eq S11|applys_eq L8]; lia. }
  assert (Brow:forall a b, a<length B -> nth a B false=true ->
      a<>H-1 -> 2*a+b=2*H+7 -> P a b (H+2) 8).
  { intros a b Hal Hab Han Haw. assert (2<=b) by lia.
    applys_eq (k5_rov R a (b-2) (H+2) 2 (H+2) 7); try lia.
    - apply Arow; assumption || lia.
    - exact G2. }
  assert (Crow:forall a b, a<length B -> nth a B false=true ->
      2*a+b=2*H+9 -> P a b (H+1) 12).
  { intros a b Hal Hab Haw. destruct (Nat.eq_dec a (H-1)) as [->|Han].
    - applys_eq S11; lia.
    - assert (2<=b) by lia.
      applys_eq (k5_rov R a (b-2) (H+2) 4 (H+1) 11); try lia.
      + apply Brow; assumption || lia.
      + exact G4. }
  assert (Drow:forall a b, a<length B -> nth a B false=true ->
      2*a+b=2*H+11 -> P a b (H+1) 14).
  { intros a b Hal Hab Haw. assert (2<=b) by lia.
    applys_eq (k5_rov R a (b-2) (H+1) 8 (H+1) 13); try lia.
    - apply Crow; assumption || lia.
    - exact L8. }
  assert (RT:K4ExactRow Q B true (2*H+13) H 17).
  { split; [lia|]. intros a b Hal Hab Haw. unfold Q,K5Q.
    assert (2<=b) by lia.
    applys_eq (k5_rov R a (b-2) (H+1) 10 H 17); try lia.
    - apply Drow; assumption || lia.
    - exact L10. }
  assert (F6:K4ExactRow Q B false (2*H+6) (H+3) 4).
  { split; [lia|]. intros a b Hal Hab Haw.
    assert (Ha:a<H+1-S).
    { destruct (Nat.lt_ge_cases a (H+1-S)); [assumption|].
      assert (nth a B false=true) by (apply Hlast; lia). congruence. }
    assert (7<=b) by lia. unfold Q,K5Q.
    applys_eq (@k5_lov5 P R a (b-7) 0 (2*H-1) (H+2)
      ltac:(unfold Q,K5Q in F0; applys_eq (proj2 F0 a (b-7) Hal Hab); lia)
      ltac:(applys_eq Z; lia)); lia. }
  assert (E3Q:Q (H+3) 0 (1+(D-2)) (4*S+12)) by
    (unfold Q,K5Q; applys_eq E3; lia).
  assert (F8:K4ExactRow Q B false (2*H+8) (D-2) (4*S+16)).
  { applys_eq (k4_exact_row_rov' Q C B false (2*H+6) (H+3) 0
      (D-2) (4*S+12) ltac:(lia) F6 E3Q ltac:(lia)); lia. }
  assert (AD2:P (D-2) (4*S+9) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
  assert (AD24:P (D-2) (4*S+13) (H+1) 12).
  { applys_eq (k5_rov R (D-2) (4*S+11) (H+2) 4 (H+1) 11);
      try lia.
    - applys_eq (k5_rov R (D-2) (4*S+9) (H+2) 2 (H+2) 7);
        try lia; [applys_eq AD2|applys_eq G2]; lia.
    - exact G4. }
  assert (AD24Q:Q (D-2) (4*S+13) (H+1) 11) by
    (unfold Q,K5Q; applys_eq AD24; lia).
  assert (F10:K4ExactRow Q B false (2*H+10) (H+1) 12).
  { applys_eq (k4_exact_row_rov Q C B false (2*H+8) (D-2)
      (4*S+13) (H+1) 11 ltac:(lia)
      ltac:(applys_eq F8; lia) AD24Q ltac:(lia)); lia. }
  assert (L8Q:Q (H+1) 8 (1+H) 12) by
    (unfold Q,K5Q; applys_eq L8; lia).
  assert (F12:K4ExactRow Q B false (2*H+12) H 16).
  { applys_eq (k4_exact_row_rov' Q C B false (2*H+10) (H+1) 8
      H 12 ltac:(lia) F10 L8Q ltac:(lia)); lia. }
  assert (N13Q:Q H 13 H 17) by
    (unfold Q,K5Q; applys_eq N13; lia).
  assert (RF:K4ExactRow Q B false (2*H+14) H 18).
  { applys_eq (k4_exact_row_rov Q C B false (2*H+12) H 13 H 17
      ltac:(lia) F12 N13Q ltac:(lia)); lia. }
  assert (P1:P (H+1) 12 H 19).
  { applys_eq (k5_rov R (H+1) 10 H 13 H 18); try lia;
      [applys_eq L10|applys_eq N13]; lia. }
  assert (P26:P (H+2) 6 (H-1) 17).
  { applys_eq (k5_rov' R (H+2) 4 (H+1) 6 (H-1) 13);
      try lia; [applys_eq G4|applys_eq L6]; lia. }
  assert (P28:P (H+2) 8 (H+1) 15).
  { applys_eq (k5_rov R (H+2) 6 (H-1) 13 (H+1) 14);
      try lia; [applys_eq P26|applys_eq S13]; lia. }
  assert (P2:P (H+2) 10 (H-1) 21).
  { applys_eq (k5_rov' R (H+2) 8 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P28|applys_eq L10]; lia. }
  assert (P32:P (H+3) 2 (H+2) 9).
  { applys_eq (k5_rov R (H+3) 0 (D-1) (4*S+9) (H+2) 8);
      try lia; [applys_eq E3|applys_eq AD1']; lia. }
  assert (P34:P (H+3) 4 H 15).
  { applys_eq (k5_rov' R (H+3) 2 (H+2) 4 H 11);
      try lia; [applys_eq P32|applys_eq G4]; lia. }
  assert (P36:P (H+3) 6 (H+1) 15).
  { applys_eq (k5_rov R (H+3) 4 H 11 (H+1) 14);
      try lia; [applys_eq P34|applys_eq N11]; lia. }
  assert (P3:P (H+3) 8 (H-1) 21).
  { applys_eq (k5_rov' R (H+3) 6 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P36|applys_eq L10]; lia. }
  assert (P42:P (H+4) 2 (H+1) 13).
  { applys_eq (k5_rov R (H+4) 0 (D-2) (4*S+13) (H+1) 12);
      try lia; [applys_eq E4|applys_eq AD24]; lia. }
  assert (P44:P (H+4) 4 H 17).
  { applys_eq (k5_rov' R (H+4) 2 (H+1) 8 H 13);
      try lia; [applys_eq P42|applys_eq L8]; lia. }
  assert (P4:P (H+4) 6 H 19).
  { applys_eq (k5_rov R (H+4) 4 H 13 H 18); try lia;
      [applys_eq P44|applys_eq N13]; lia. }
  assert (AD3:P (D-3) (4*S+11) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
  assert (AD36:P (D-3) (4*S+17) (H+1) 14).
  { applys_eq (k5_rov R (D-3) (4*S+15) (H+1) 8 (H+1) 13);
      try lia.
    - applys_eq (k5_rov R (D-3) (4*S+13) (H+2) 4 (H+1) 11);
        try lia.
      + applys_eq (k5_rov R (D-3) (4*S+11) (H+2) 2 (H+2) 7);
          try lia; [applys_eq AD3|applys_eq G2]; lia.
      + exact G4.
    - exact L8. }
  assert (P52:P (H+5) 2 (H+1) 15).
  { applys_eq (k5_rov R (H+5) 0 (D-3) (4*S+17) (H+1) 14);
      try lia; [applys_eq E5|applys_eq AD36]; lia. }
  assert (P5:P (H+5) 4 (H-1) 21).
  { applys_eq (k5_rov' R (H+5) 2 (H+1) 10 (H-1) 17);
      try lia; [applys_eq P52|applys_eq L10]; lia. }
  assert (AD4:P (D-4) (4*S+13) (H+2) 6).
  { apply Arow; [rewrite Hlen; lia|apply Hwin; lia|lia|lia]. }
  assert (AD48:P (D-4) (4*S+21) H 18).
  { applys_eq (k5_rov R (D-4) (4*S+19) (H+1) 10 H 17);
      try lia.
    - applys_eq (k5_rov R (D-4) (4*S+17) (H+1) 8 (H+1) 13);
        try lia.
      + applys_eq (k5_rov R (D-4) (4*S+15) (H+2) 4 (H+1) 11);
          try lia.
        * applys_eq (k5_rov R (D-4) (4*S+13) (H+2) 2 (H+2) 7);
            try lia; [applys_eq AD4|applys_eq G2]; lia.
        * exact G4.
      + exact L8.
    - exact L10. }
  assert (P6:P (H+6) 2 H 19).
  { applys_eq (k5_rov R (H+6) 0 (D-4) (4*S+21) H 18);
      try lia; [applys_eq E6|applys_eq AD48]; lia. }
  unfold K5ScanPayload.
  split; [exact (conj B0 (conj B1 B2))|].
  split; [exact Hdrop|]. split; [exact RT|]. split; [exact RF|].
  split; [|exact E7]. unfold K5Tail. repeat split; assumption.
Qed.

End K5Boundary.
