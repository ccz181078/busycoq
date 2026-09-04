Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Boundary.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Section K4BoundaryShared.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K4SimpleRules P.

Lemma k4_type2_pretail B H S D:
  3<=S -> 4<=D -> length B=H+1 -> nth H B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4Type2PreFront P B H S D -> K4Type2PreTail P H S D.
Proof.
  intros HS HD Hlen BH Hbits [Hhs [E1 [E2 [E3 [RT0 Dent]]]]].
  destruct RT0 as [dt [Hdt RT0]]. assert (dt=7) by lia. subst dt.
  assert (T:forall z t, z+t=H -> z<length B -> z<>H-1 ->
      nth z B false=true -> P z (2*t+7) (H+2) 7).
  { intros. apply RT0; assumption || lia. }
  assert (A:P (H+2) 4 (H+1) 10) by
    (applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia;
      applys_eq E2; lia).
  assert (B1:P (H+1) 6 H 12) by
    (applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia).
  assert (TH:P H 7 (H+2) 7) by
    (exact (T H 0 ltac:(lia) ltac:(rewrite Hlen; lia) ltac:(lia) BH)).
  assert (H9:P H 9 (H+1) 11) by
    (eapply (k4_rov R); [exact TH|exact A]).
  assert (C1:P (H+1) 8 (H+1) 12) by
    (eapply (k4_rov R); [exact B1|exact H9]).
  assert (D1:P (H+1) 10 H 16) by
    (eapply (k4_rov' R); [exact C1|applys_eq C1; lia]).
  assert (H11:P H 11 (H+1) 13) by
    (eapply (k4_rov R); [exact H9|exact C1]).
  assert (H13:P H 13 H 17) by
    (eapply (k4_rov R); [exact H11|exact D1]).
  assert (U:forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+9) (H+1) 11).
  { intros z t HT. applys_eq (k4_rov R z (2*t+7)
      (H+2) 4 (H+1) 10); try lia; assumption. }
  assert (V:forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+11) (H+1) 13).
  { intros z t HT. applys_eq (k4_rov R z (2*t+9)
      (H+1) 8 (H+1) 12); try lia; [exact (U z t HT)|exact C1]. }
  assert (W:forall z t, P z (2*t+7) (H+2) 7 ->
      P z (2*t+13) H 17).
  { intros z t HT. applys_eq (k4_rov R z (2*t+11)
      (H+1) 10 H 16); try lia; [exact (V z t HT)|exact D1]. }
  assert (TD:P D (4*S+7) (H+2) 7).
  { replace (4*S+7) with (2*(2*S)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (Dent1:P (H-1) 11 (H+1) 11).
  { applys_eq (k4_rov' R (H-1) 9 D (4*S+7) (H+1) 7);
      try lia; [applys_eq Dent|applys_eq TD]; lia. }
  assert (Hm13:P (H-1) 13 (H+1) 13) by
    (eapply (k4_rov R); [exact Dent1|exact C1]).
  assert (Hm15:P (H-1) 15 H 17) by
    (eapply (k4_rov R); [exact Hm13|exact D1]).
  assert (Hm17:P (H-1) 17 (H-1) 21) by
    (eapply (k4_rov' R); [exact Hm15|applys_eq H13; lia]).
  assert (E4:P (H+4) 0 (D-1) (4*S+14)) by
    (applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia;
      applys_eq E3; lia).
  assert (E5:P (H+5) 0 (D-2) (4*S+18)) by
    (applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia;
      applys_eq E4; lia).
  assert (E6:P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
      applys_eq E5; lia).
  assert (E7:P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
      applys_eq E6; lia).
  assert (P1:P (H+1) 12 H 18) by
    (eapply (k4_rov R); [exact D1|exact H13]).
  assert (A6:P (H+2) 6 (H-1) 16) by
    (eapply (k4_rov' R); [exact A|applys_eq B1; lia]).
  assert (A8:P (H+2) 8 (H+1) 14) by
    (eapply (k4_rov R); [exact A6|exact Hm13]).
  assert (P2:P (H+2) 10 (H-1) 20) by
    (eapply (k4_rov' R); [exact A8|applys_eq D1; lia]).
  assert (G32:P (H+3) 2 (H+2) 8).
  { applys_eq (k4_rov R (H+3) 0 D (4*S+7) (H+2) 7); try lia;
      [applys_eq E3; lia|exact TD]. }
  assert (G34:P (H+3) 4 H 14) by
    (eapply (k4_rov' R); [exact G32|applys_eq A; lia]).
  assert (G36:P (H+3) 6 (H+1) 14) by
    (eapply (k4_rov R); [exact G34|exact H11]).
  assert (P3:P (H+3) 8 (H-1) 20) by
    (eapply (k4_rov' R); [exact G36|applys_eq D1; lia]).
  assert (TD1:P (D-1) (4*S+9) (H+2) 7).
  { replace (4*S+9) with (2*(2*S+1)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (G42:P (H+4) 2 (H+1) 12).
  { applys_eq (k4_rov R (H+4) 0 (D-1) (4*S+11) (H+1) 11);
      try lia; [applys_eq E4; lia|].
    applys_eq (U (D-1) (2*S+1)); try lia. applys_eq TD1; lia. }
  assert (G44:P (H+4) 4 H 16) by
    (eapply (k4_rov' R); [exact G42|applys_eq C1; lia]).
  assert (P4:P (H+4) 6 H 18) by
    (eapply (k4_rov R); [exact G44|exact H13]).
  assert (TD2:P (D-2) (4*S+11) (H+2) 7).
  { replace (4*S+11) with (2*(2*S+2)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (G52:P (H+5) 2 (H+1) 14).
  { applys_eq (k4_rov R (H+5) 0 (D-2) (4*S+15) (H+1) 13);
      try lia; [applys_eq E5; lia|].
    applys_eq (V (D-2) (2*S+2)); try lia. applys_eq TD2; lia. }
  assert (P5:P (H+5) 4 (H-1) 20) by
    (eapply (k4_rov' R); [exact G52|applys_eq D1; lia]).
  assert (TD3:P (D-3) (4*S+13) (H+2) 7).
  { replace (4*S+13) with (2*(2*S+3)+7) by lia.
    apply T; [lia|rewrite Hlen; lia|lia|apply Hbits; lia]. }
  assert (P6:P (H+6) 2 H 18).
  { applys_eq (k4_rov R (H+6) 0 (D-3) (4*S+19) H 17);
      try lia; [applys_eq E6; lia|].
    applys_eq (W (D-3) (2*S+3)); try lia. applys_eq TD3; lia. }
  unfold K4Type2PreTail. repeat split; assumption.
Qed.

Lemma k4_type2_tail B H S D:
  H=2*S+D -> 4<=D -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4ExactRow P B true (2*H+15) (H-1) 21 ->
  K4Type2PreTail P H S D ->
  forall j, j<=6 -> P (H+7-j) (2+2*j) (H-1) 22.
Proof.
  intros Hhs HD Hlen BH BHm Hbits [_ RT] Hpre.
  destruct Hpre as [P1 [P2 [P3 [P4 [P5 [P6 P7]]]]]].
  assert (finish:forall a b c d,
      P a b c (3+d) -> c<length B -> nth c B false=true ->
      2*c+d=2*H+15 -> P a (2+b) (H-1) 22).
  { intros a b c d HP Hcl Hcb Hcw.
    applys_eq (k4_rov R a b c d (H-1) 21); try lia.
    - exact HP.
    - apply RT; assumption. }
  intros j Hj.
  assert (j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6) by lia.
  repeat match goal with H0:_ \/ _ |- _ => destruct H0 as [->|H0] end;
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

Lemma k4_type4_pretail B H S D:
  3<=S -> 5<=D -> length B=H+1 ->
  nth H B false=true -> nth (H-1) B false=true ->
  (forall z, D-4<=z<=D -> nth z B false=true) ->
  K4Type4PreFront P B H S D -> K4Type4PreTail P H S D.
Proof.
  intros HS HD Hlen BH BHm Hbits
    [Hhs [RT0 [E1 [E2 [E3 [E4 E5]]]]]].
  destruct RT0 as [dt [Hdt RT0]]. assert (dt=11) by lia. subst dt.
  assert (T:forall z t, z+t=H -> z<length B ->
      nth z B false=true -> P z (2*t+9) (H+1) 11).
  { intros. apply RT0; assumption || lia. }
  assert (C10:P (H+1) 10 H 16) by
    (applys_eq (k4_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq E1; lia).
  assert (TH:P H 9 (H+1) 11) by
    (exact (T H 0 ltac:(lia) ltac:(rewrite Hlen; lia) BH)).
  assert (THm:P (H-1) 11 (H+1) 11) by
    (exact (T (H-1) 1 ltac:(lia) ltac:(rewrite Hlen; lia) BHm)).
  assert (U:forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+11) (H+1) 13).
  { intros z t HT. applys_eq (k4_rov R z (2*t+9)
      (H+1) 8 (H+1) 12); try lia; assumption. }
  assert (V:forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+13) H 17).
  { intros z t HT. applys_eq (k4_rov R z (2*t+11)
      (H+1) 10 H 16); try lia; [exact (U z t HT)|exact C10]. }
  assert (VH:P H 13 H 17) by exact (V H 0 TH).
  assert (W:forall z t, P z (2*t+9) (H+1) 11 ->
      P z (2*t+15) (H-1) 21).
  { intros z t HT. applys_eq (k4_rov' R z (2*t+13)
      H 13 (H-1) 17); try lia; [exact (V z t HT)|applys_eq VH; lia]. }
  assert (H15:P H 15 (H-1) 21) by exact (W H 0 TH).
  assert (Hm17:P (H-1) 17 (H-1) 21) by
    (applys_eq (W (H-1) 1 THm); lia).
  assert (C12:P (H+1) 12 H 18) by
    (eapply (k4_rov R); [exact C10|exact VH]).
  assert (P1:P (H+1) 14 (H-1) 22) by
    (eapply (k4_rov R); [exact C12|exact H15]).
  assert (X28:P (H+2) 8 (H+1) 14) by
    (eapply (k4_rov R); [exact E2|exact (U (H-1) 1 THm)]).
  assert (X210:P (H+2) 10 (H-1) 20) by
    (eapply (k4_rov' R); [exact X28|applys_eq C10; lia]).
  assert (P2:P (H+2) 12 (H-1) 22) by
    (eapply (k4_rov R); [exact X210|exact Hm17]).
  assert (X36:P (H+3) 6 (H+1) 14) by
    (eapply (k4_rov R); [exact E3|exact (U H 0 TH)]).
  assert (X38:P (H+3) 8 (H-1) 20) by
    (eapply (k4_rov' R); [exact X36|applys_eq C10; lia]).
  assert (P3:P (H+3) 10 (H-1) 22) by
    (eapply (k4_rov R); [exact X38|exact Hm17]).
  assert (X44:P (H+4) 4 H 16) by
    (eapply (k4_rov' R); [exact E4|applys_eq E1; lia]).
  assert (X46:P (H+4) 6 H 18) by
    (eapply (k4_rov R); [exact X44|exact VH]).
  assert (P4:P (H+4) 8 (H-1) 22) by
    (eapply (k4_rov R); [exact X46|exact H15]).
  assert (TD2:P (D-2) (4*S+13) (H+1) 11).
  { replace (4*S+13) with (2*(2*S+2)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (X52:P (H+5) 2 (H+1) 14).
  { applys_eq (k4_rov R (H+5) 0 (D-2) (4*S+15) (H+1) 13);
      try lia; [applys_eq E5; lia|].
    applys_eq (U (D-2) (2*S+2)); try lia. applys_eq TD2; lia. }
  assert (X54:P (H+5) 4 (H-1) 20) by
    (eapply (k4_rov' R); [exact X52|applys_eq C10; lia]).
  assert (P5:P (H+5) 6 (H-1) 22) by
    (eapply (k4_rov R); [exact X54|exact Hm17]).
  assert (E6:P (H+6) 0 (D-3) (4*S+22)) by
    (applys_eq (k4_inc01 R (H+5) (D-3) (4*S+18)); try lia;
      applys_eq E5; lia).
  assert (TD3:P (D-3) (4*S+15) (H+1) 11).
  { replace (4*S+15) with (2*(2*S+3)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (X62:P (H+6) 2 H 18).
  { applys_eq (k4_rov R (H+6) 0 (D-3) (4*S+19) H 17);
      try lia; [applys_eq E6; lia|].
    applys_eq (V (D-3) (2*S+3)); try lia. applys_eq TD3; lia. }
  assert (P6:P (H+6) 4 (H-1) 22) by
    (eapply (k4_rov R); [exact X62|exact H15]).
  assert (E7:P (H+7) 0 (D-4) (4*S+26)) by
    (applys_eq (k4_inc01 R (H+6) (D-4) (4*S+22)); try lia;
      applys_eq E6; lia).
  assert (TD4:P (D-4) (4*S+17) (H+1) 11).
  { replace (4*S+17) with (2*(2*S+4)+9) by lia.
    apply T; [lia|rewrite Hlen; lia|apply Hbits; lia]. }
  assert (P7:P (H+7) 2 (H-1) 22).
  { applys_eq (k4_rov R (H+7) 0 (D-4) (4*S+23) (H-1) 21);
      try lia; [applys_eq E7; lia|].
    applys_eq (W (D-4) (2*S+4)); try lia. applys_eq TD4; lia. }
  assert (P8:P (H+8) 0 (D-5) (4*S+30)) by
    (applys_eq (k4_inc01 R (H+7) (D-5) (4*S+26)); try lia;
      applys_eq E7; lia).
  unfold K4Type4PreTail. repeat split; assumption.
Qed.

Lemma k4_type4_tail B H S D:
  H=2*S+D -> 5<=D -> length B=H+1 ->
  nth (H-1) B false=true -> nth (D-5) B false=true ->
  K4ExactRow P B true (2*H+17) (H-2) 25 ->
  K4Type4PreTail P H S D ->
  forall j, j<=7 -> P (H+8-j) (2+2*j) (H-2) 26.
Proof.
  intros Hhs HD Hlen BHm BD [_ RT] Hpre.
  destruct Hpre as [P1 [P2 [P3 [P4 [P5 [P6 [P7 P8]]]]]]].
  assert (finish:forall a b c d,
      P a b c (3+d) -> c<length B -> nth c B false=true ->
      2*c+d=2*H+17 -> P a (2+b) (H-2) 26).
  { intros a b c d HP Hcl Hcb Hcw.
    applys_eq (k4_rov R a b c d (H-2) 25); try lia.
    - exact HP.
    - apply RT; assumption. }
  intros j Hj.
  assert (j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7)
    by lia.
  repeat match goal with H0:_ \/ _ |- _ => destruct H0 as [->|H0] end;
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

End K4BoundaryShared.
