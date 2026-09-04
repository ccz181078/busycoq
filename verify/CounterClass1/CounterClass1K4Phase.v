Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4ScanCore.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Section K4PhaseProbe.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4SimpleRules P.

Lemma k4_scan_endfan_t4_data B H S D k:
  K4ScanData P K4T4 B H S D k -> K4HeadBits K4T4 B ->
  K4EndFan P K4T2 (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k).
Proof.
  intros HS [B0 [B1 B2]].
  assert (HC := k4_scan_core_data P R K4T4 B H S D k HS).
  unfold K4ScanData in HS; cbn in HS.
  destruct HS as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [R0 [R1 [Htail Hex]]]]]]]]]].
  unfold K4CoreEnd in HC.
  set (Hp:=2*H+k+7) in *.
  set (Sp:=2*S+k+3) in *.
  set (Dp:=2*D+1-k) in *.
  set (A:=H+D+3) in *.
  set (W:=2*Hp-1) in *.
  destruct HC as (x&y&HP&RTX&RFY&Hpair&Hreach&HD&HE&Hzeros&RTW&RFW&Hfirst&Hbridge&HTop).
  destruct (k4_terminal_pair_t4 B (W-4) x y B0 B1 B2 Hpair Hreach HP)
    as [-> ->].
  destruct (k4_endpoint_last2_t4 P R B (W-4) (Hp-2) (Dp+5)
      (4*Sp-10) B0 B1 B2 ltac:(lia) ltac:(lia)
      ltac:(applys_eq HP; lia) ltac:(applys_eq RTX; lia)
      ltac:(applys_eq RFY; lia) HD HE ltac:(lia) ltac:(lia)) as
    [HDf [HDpre [HE0 [Hdent Hend]]]].
  assert (Hextlen: length (k4_extend B (D+3) Sp)=Hp+1) by
    (rewrite k4_extend_length,Hlen; unfold Hp,Sp; lia).
  destruct RTW as [dt [Hdt RTW]].
  destruct RFW as [df [Hdf RFW]].
  assert (Hfalse: K4ExactRow P (k4_extend B (D+3) Sp) false
      W 0 (2*Hp+3)).
  { split; [unfold W; lia|]. intros a b Hal Hab Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold: nth a B false=true).
      { rewrite k4_extend_old in Hab; [|lia]. destruct (nth a B false); cbn in *;
          congruence. }
      applys_eq (RTW a b Ha Hold); try lia.
    - assert (HaA: a=length B+(D+3)).
      { apply k4_extend_false_suffix with (T:=Sp); assumption || lia. }
      subst a. destruct HTop as [bt [d [Haw' [Hd HPa]]]].
      applys_eq HPa; rewrite Hlen in *; unfold A,W in *; lia. }
  assert (Htrue: forall a b,
      a<length (k4_extend B (D+3) Sp) ->
      nth a (k4_extend B (D+3) Sp) false=true ->
      a<>Hp -> a<>Hp-1 -> 2*a+b=2*Hp -> P a b 0 (2*Hp+4)).
  { intros a b Hal Hab HaHp HaHm Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold: nth a B false=false).
      { rewrite k4_extend_old in Hab; [|lia]. destruct (nth a B false); cbn in *;
          congruence. }
      applys_eq (RFW a b Ha Hold); try lia.
    - destruct (k4_extend_true_suffix B (D+3) Sp a ltac:(lia) Hal Hab)
        as [Ha1|Ha2].
      + assert (HH: H+1<=a<=A) by (rewrite Hlen in Ha1; unfold A; lia).
        destruct (Hfirst a HH) as [ba [da [Haw' [Hd HPa]]]].
        applys_eq HPa; unfold W in *; lia.
      + rewrite Hlen in Ha2.
        destruct (Compare_dec.le_lt_dec (A+6) a) as [HA6|Ha6].
        * destruct (Compare_dec.lt_dec a (Hp-2)) as [Ham2|Ham2].
          -- assert (Hj: a=A+6+(a-(A+6))) by lia. rewrite Hj.
             destruct (Hzeros (a-(A+6)) ltac:(unfold Sp; lia))
               as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
          -- assert (a=Hp-2) by lia. subst a.
             destruct HE0 as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
        * assert (HH: A+2<=a<=A+5) by lia.
          destruct (Hbridge a HH) as [ba [da [Haw' [Hd HPa]]]].
          applys_eq HPa; unfold W in *; lia. }
  unfold K4EndFan. fold Hp Sp Dp W.
  split; [lia|].
  split; [applys_eq Hfalse; unfold W; lia|].
  split; [intros _; applys_eq (RTW 0 W ltac:(lia) B0 ltac:(lia)); lia|].
  split; [intros a b Hal Hab HaHp Hprev Haw;
    exact (Htrue a b Hal Hab HaHp (Hprev eq_refl) Haw)|].
  split; [applys_eq Hend; lia|].
  split; [intros _; applys_eq Hdent; lia|].
  intros _.
    destruct HDpre as [bd [dd [Hin [Hout HPd]]]].
    applys_eq HPd; unfold W in *; lia.
Qed.

Lemma k4_scan_endfan_t2_data B H S D k:
  K4ScanData P K4T2 B H S D k -> K4HeadBits K4T2 B ->
  K4EndFan P K4T4 (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k).
Proof.
  intros HS [B0 [B1 B2]].
  assert (HC := k4_scan_core_data P R K4T2 B H S D k HS).
  unfold K4ScanData in HS; cbn in HS.
  destruct HS as [Hlen [Hhs [Hlarge [Hk [Hs [Hbase
    [Hdrop [R0 [R1 [Htail Hex]]]]]]]]]].
  unfold K4CoreEnd in HC.
  set (Hp:=2*H+k+7) in *.
  set (Sp:=2*S+k+3) in *.
  set (Dp:=2*D+1-k) in *.
  set (A:=H+D+3) in *.
  set (W:=2*Hp-1) in *.
  destruct HC as (x&y&HP&RTX&RFY&Hpair&Hreach&HD&HE&Hzeros&RTW&RFW&Hfirst&Hbridge&HTop).
  destruct (k4_terminal_pair_t2 B (W-4) x y B0 B1 B2 Hpair Hreach HP)
    as [-> ->].
  destruct (k4_endpoint_last2_t2 P R B (W-4) (Hp-2) (Dp+5)
      (4*Sp-10) B0 B1 B2 ltac:(lia) ltac:(lia)
      ltac:(applys_eq HP; lia) ltac:(applys_eq RTX; lia)
      ltac:(applys_eq RFY; lia) HD HE ltac:(lia) ltac:(lia)) as
    [HDf [HE0 [HE1 Hend]]].
  assert (Hextlen: length (k4_extend B (D+3) Sp)=Hp+1) by
    (rewrite k4_extend_length,Hlen; unfold Hp,Sp; lia).
  destruct RTW as [dt [Hdt RTW]].
  destruct RFW as [df [Hdf RFW]].
  assert (Hfalse: K4ExactRow P (k4_extend B (D+3) Sp) false
      W 0 (2*Hp+3)).
  { split; [unfold W; lia|]. intros a b Hal Hab Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold: nth a B false=true).
      { rewrite k4_extend_old in Hab; [|lia]. destruct (nth a B false); cbn in *;
          congruence. }
      applys_eq (RTW a b Ha Hold); try lia.
    - assert (HaA: a=length B+(D+3)).
      { apply k4_extend_false_suffix with (T:=Sp); assumption || lia. }
      subst a. destruct HTop as [bt [d [Haw' [Hd HPa]]]].
      applys_eq HPa; rewrite Hlen in *; unfold A,W in *; lia. }
  assert (Htrue: forall a b,
      a<length (k4_extend B (D+3) Sp) ->
      nth a (k4_extend B (D+3) Sp) false=true ->
      a<>Hp -> 2*a+b=2*Hp -> P a b 0 (2*Hp+4)).
  { intros a b Hal Hab HaHp Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold: nth a B false=false).
      { rewrite k4_extend_old in Hab; [|lia]. destruct (nth a B false); cbn in *;
          congruence. }
      applys_eq (RFW a b Ha Hold); try lia.
    - destruct (k4_extend_true_suffix B (D+3) Sp a ltac:(lia) Hal Hab)
        as [Ha1|Ha2].
      + assert (HH: H+1<=a<=A) by (rewrite Hlen in Ha1; unfold A; lia).
        destruct (Hfirst a HH) as [ba [da [Haw' [Hd HPa]]]].
        applys_eq HPa; unfold W in *; lia.
      + rewrite Hlen in Ha2.
        destruct (Compare_dec.le_lt_dec (A+6) a) as [HA6|Ha6].
        * destruct (Compare_dec.lt_dec a (Hp-2)) as [Ham2|Ham2].
          -- assert (Hj: a=A+6+(a-(A+6))) by lia. rewrite Hj.
             destruct (Hzeros (a-(A+6)) ltac:(unfold Sp; lia))
               as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
          -- assert (Haedge: a=Hp-2 \/ a=Hp-1) by lia.
             destruct Haedge as [Haedge|Haedge]; subst a.
             ++ destruct HE0 as [ba [da [Haw' [Hd HPa]]]].
                applys_eq HPa; unfold W in *; lia.
             ++ destruct HE1 as [ba [da [Haw' [Hd HPa]]]].
                applys_eq HPa; unfold W in *; lia.
        * assert (HH: A+2<=a<=A+5) by lia.
          destruct (Hbridge a HH) as [ba [da [Haw' [Hd HPa]]]].
          applys_eq HPa; unfold W in *; lia. }
  unfold K4EndFan. fold Hp Sp Dp W.
  split; [lia|].
  split; [applys_eq Hfalse; unfold W; lia|].
  split; [discriminate|].
  split; [intros a b Hal Hab HaHp _ Haw; eapply Htrue; eauto|].
  split; [applys_eq Hend; lia|].
  split; discriminate.
Qed.

Lemma k4_scan_endfan_t4 runs B H S D k:
  K4ScanStart P K4T4 runs B H S D k -> K4HeadBits K4T4 B ->
  K4EndFan P K4T2 (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k).
Proof.
  intros HS.
  apply k4_scan_endfan_t4_data.
  exact (k4_scan_start_data P K4T4 runs B H S D k HS).
Qed.

Lemma k4_scan_endfan_t2 runs B H S D k:
  K4ScanStart P K4T2 runs B H S D k -> K4HeadBits K4T2 B ->
  K4EndFan P K4T4 (k4_extend B (D+3) (2*S+k+3))
    (2*H+k+7) (2*S+k+3) (2*D+1-k).
Proof.
  intros HS.
  apply k4_scan_endfan_t2_data.
  exact (k4_scan_start_data P K4T2 runs B H S D k HS).
Qed.

End K4PhaseProbe.
