Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Words
  BusyCoq.CounterClass1.CounterClass1K5Common BusyCoq.CounterClass1.CounterClass1K5Scan BusyCoq.CounterClass1.CounterClass1K5Words.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.

Definition K5EndFan (P:nat->nat->nat->nat->Prop)
    (kind:K4Kind) (B:list bool) (H S D:nat) : Prop :=
  H=2*S+D /\
  K4ExactRow (K5Q P) B false (2*H-1) 0 (2*H+3) /\
  (kind=K4T2 -> K5Q P 0 (2*H-1) 0 (2*H+3)) /\
  (forall a b, a<length B -> nth a B false=true -> a<>H ->
    (kind=K4T2 -> a<>H-1) -> 2*a+b=2*H ->
    K5Q P a b 0 (2*H+4)) /\
  K5Q P H 0 (D+2) (4*S) /\
  (kind=K4T2 -> K5Q P (H-1) 0 (D+3) (4*S-4)) /\
  (kind=K4T2 -> K5Q P (D+3) (4*S-8) 0 (2*H+2)).

Section K5Phase.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.
Let Q:=K5Q P.
Let C:=k5_q_core_rules P R.

Lemma k5_scan_endfan_t4 runs B H S D k:
  K5ScanStart P K4T4 runs B H S D k ->
  K5EndFan P K4T2 (k4_extend B (D+2) (2*S+k+4))
    (2*H+k+7) (2*S+k+4) (2*D-k-1).
Proof.
  intros HS0.
  pose proof HS0 as HS.
  unfold K5ScanStart,K5ScanPayload in HS.
  destruct HS as [Hshape [Hbits [Hhead
    [[B0 [B1 B2]] [Hdrop [R0 [R1 [Htail Hex]]]]]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk Hs]]]]]]].
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  assert (HC:=k5_scan_core P R K4T4 runs B H S D k HS0).
  unfold K5CoreEnd in HC.
  set (Hp:=2*H+k+7) in *.
  set (Sp:=2*S+k+4) in *.
  set (Dp:=2*D-k-1) in *.
  set (A:=H+D+2) in *.
  set (W:=2*Hp-1) in *.
  destruct HC as
    (x&y&HP&RTX&RFY&Hpair&Hreach&HD&HE&Hzeros&RTW&RFW&Hfirst&Hbridge&HTop).
  destruct (k4_terminal_pair_t4 B (W-4) x y B0 B1 B2 Hpair Hreach HP)
    as [-> ->].
  assert (HEQ:Q (Hp-2) 0 (Dp+4) (4*Sp-8)).
  { unfold Q,K5Q. applys_eq HE; lia. }
  destruct (k4_endpoint_last2_t4 Q C B (W-4) (Hp-2) (Dp+4)
      (4*Sp-8) B0 B1 B2 ltac:(lia) ltac:(lia)
      ltac:(applys_eq HP; lia) ltac:(applys_eq RTX; lia)
      ltac:(applys_eq RFY; lia) HD HEQ ltac:(lia) ltac:(lia)) as
    [HDf [HDpre [HE0 [Hdent Hend]]]].
  assert (Hseed:Q (Dp+3) (4*Sp-8) 0 (2*Hp+2)).
  { destruct HDpre as (b&d&Hb&Hd&HPd).
    applys_eq HPd; unfold W in *; lia. }
  assert (Hextlen:length (k4_extend B (D+2) Sp)=Hp+1) by
    (rewrite k4_extend_length,Hlen; unfold Hp,Sp; lia).
  destruct RTW as [dt [Hdt RTW]].
  destruct RFW as [df [Hdf RFW]].
  assert (Hfalse:K4ExactRow Q (k4_extend B (D+2) Sp) false
      W 0 (2*Hp+3)).
  { split; [unfold W; lia|]. intros a b Hal Hab Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold:nth a B false=true).
      { rewrite k4_extend_old in Hab; [|lia].
        destruct (nth a B false); cbn in *; congruence. }
      applys_eq (RTW a b Ha Hold Haw); try lia.
    - assert (HaA:a=length B+(D+2)).
      { apply k4_extend_false_suffix with (T:=Sp); assumption || lia. }
      subst a. destruct HTop as [bt [d [Haw' [Hd HPa]]]].
      applys_eq HPa; rewrite Hlen in *; unfold A,W in *; lia. }
  assert (Htrue:forall a b,
      a<length (k4_extend B (D+2) Sp) ->
      nth a (k4_extend B (D+2) Sp) false=true ->
      a<>Hp -> a<>Hp-1 -> 2*a+b=2*Hp -> Q a b 0 (2*Hp+4)).
  { intros a b Hal Hab HaHp HaHm Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold:nth a B false=false).
      { rewrite k4_extend_old in Hab; [|lia].
        destruct (nth a B false); cbn in *; congruence. }
      applys_eq (RFW a b Ha Hold ltac:(unfold W; lia)); try lia.
    - destruct (k4_extend_true_suffix B (D+2) Sp a ltac:(lia) Hal Hab)
        as [Ha1|Ha2].
      + assert (HH:H+1<=a<=A) by
          (rewrite Hlen in Ha1; unfold A; lia).
        destruct (Hfirst a HH) as [ba [da [Haw' [Hd HPa]]]].
        applys_eq HPa; unfold W in *; lia.
      + rewrite Hlen in Ha2.
        destruct (Compare_dec.le_lt_dec (A+6) a) as [HA6|Ha6].
        * destruct (Compare_dec.lt_dec a (Hp-2)) as [Ham2|Ham2].
          -- replace a with (A+6+(a-(A+6))) by lia.
             destruct (Hzeros (a-(A+6)) ltac:(unfold Sp; lia))
               as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
          -- assert (a=Hp-2) by lia. subst a.
             destruct HE0 as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
        * assert (HH:A+2<=a<=A+5) by lia.
          destruct (Hbridge a HH) as [ba [da [Haw' [Hd HPa]]]].
          applys_eq HPa; unfold W in *; lia. }
  unfold K5EndFan. fold Hp Sp Dp W.
  split; [lia|]. split; [exact Hfalse|]. split.
  - intros _. apply (proj2 Hfalse); try lia.
    rewrite k4_extend_old by lia. rewrite B0. reflexivity.
  - split.
    + intros a b Hal Hab HaHp Hprev Haw.
    exact (Htrue a b Hal Hab HaHp (Hprev eq_refl) Haw).
    + split; [applys_eq Hend; lia|]. split.
      * intros _. applys_eq Hdent; lia.
      * intros _. exact Hseed.
Qed.

Lemma k5_scan_endfan_t2 runs B H S D k:
  K5ScanStart P K4T2 runs B H S D k ->
  K5EndFan P K4T4 (k4_extend B (D+2) (2*S+k+4))
    (2*H+k+7) (2*S+k+4) (2*D-k-1).
Proof.
  intros HS0.
  pose proof HS0 as HS.
  unfold K5ScanStart,K5ScanPayload in HS.
  destruct HS as [Hshape [Hbits [Hhead
    [[B0 [B1 B2]] [Hdrop [R0 [R1 [Htail Hex]]]]]]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk Hs]]]]]]].
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  assert (HC:=k5_scan_core P R K4T2 runs B H S D k HS0).
  unfold K5CoreEnd in HC.
  set (Hp:=2*H+k+7) in *.
  set (Sp:=2*S+k+4) in *.
  set (Dp:=2*D-k-1) in *.
  set (A:=H+D+2) in *.
  set (W:=2*Hp-1) in *.
  destruct HC as
    (x&y&HP&RTX&RFY&Hpair&Hreach&HD&HE&Hzeros&RTW&RFW&Hfirst&Hbridge&HTop).
  destruct (k4_terminal_pair_t2 B (W-4) x y B0 B1 B2 Hpair Hreach HP)
    as [-> ->].
  assert (HEQ:Q (Hp-2) 0 (Dp+4) (4*Sp-8)).
  { unfold Q,K5Q. applys_eq HE; lia. }
  destruct (k4_endpoint_last2_t2 Q C B (W-4) (Hp-2) (Dp+4)
      (4*Sp-8) B0 B1 B2 ltac:(lia) ltac:(lia)
      ltac:(applys_eq HP; lia) ltac:(applys_eq RTX; lia)
      ltac:(applys_eq RFY; lia) HD HEQ ltac:(lia) ltac:(lia)) as
    [HDf [HE0 [HE1 Hend]]].
  assert (Hextlen:length (k4_extend B (D+2) Sp)=Hp+1) by
    (rewrite k4_extend_length,Hlen; unfold Hp,Sp; lia).
  destruct RTW as [dt [Hdt RTW]].
  destruct RFW as [df [Hdf RFW]].
  assert (Hfalse:K4ExactRow Q (k4_extend B (D+2) Sp) false
      W 0 (2*Hp+3)).
  { split; [unfold W; lia|]. intros a b Hal Hab Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold:nth a B false=true).
      { rewrite k4_extend_old in Hab; [|lia].
        destruct (nth a B false); cbn in *; congruence. }
      applys_eq (RTW a b Ha Hold Haw); try lia.
    - assert (HaA:a=length B+(D+2)).
      { apply k4_extend_false_suffix with (T:=Sp); assumption || lia. }
      subst a. destruct HTop as [bt [d [Haw' [Hd HPa]]]].
      applys_eq HPa; rewrite Hlen in *; unfold A,W in *; lia. }
  assert (Htrue:forall a b,
      a<length (k4_extend B (D+2) Sp) ->
      nth a (k4_extend B (D+2) Sp) false=true ->
      a<>Hp -> 2*a+b=2*Hp -> Q a b 0 (2*Hp+4)).
  { intros a b Hal Hab HaHp Haw.
    destruct (Compare_dec.lt_dec a (length B)) as [Ha|Ha].
    - assert (Hold:nth a B false=false).
      { rewrite k4_extend_old in Hab; [|lia].
        destruct (nth a B false); cbn in *; congruence. }
      applys_eq (RFW a b Ha Hold ltac:(unfold W; lia)); try lia.
    - destruct (k4_extend_true_suffix B (D+2) Sp a ltac:(lia) Hal Hab)
        as [Ha1|Ha2].
      + assert (HH:H+1<=a<=A) by
          (rewrite Hlen in Ha1; unfold A; lia).
        destruct (Hfirst a HH) as [ba [da [Haw' [Hd HPa]]]].
        applys_eq HPa; unfold W in *; lia.
      + rewrite Hlen in Ha2.
        destruct (Compare_dec.le_lt_dec (A+6) a) as [HA6|Ha6].
        * destruct (Compare_dec.lt_dec a (Hp-2)) as [Ham2|Ham2].
          -- replace a with (A+6+(a-(A+6))) by lia.
             destruct (Hzeros (a-(A+6)) ltac:(unfold Sp; lia))
               as [ba [da [Haw' [Hd HPa]]]].
             applys_eq HPa; unfold W in *; lia.
          -- assert (Haedge:a=Hp-2 \/ a=Hp-1) by lia.
             destruct Haedge as [Haedge|Haedge].
             ++ subst a. destruct HE0 as [ba [da [Haw' [Hd HPa]]]].
                applys_eq HPa; unfold W in *; lia.
             ++ subst a. destruct HE1 as [ba [da [Haw' [Hd HPa]]]].
                applys_eq HPa; unfold W in *; lia.
        * assert (HH:A+2<=a<=A+5) by lia.
          destruct (Hbridge a HH) as [ba [da [Haw' [Hd HPa]]]].
          applys_eq HPa; unfold W in *; lia. }
  unfold K5EndFan. fold Hp Sp Dp W.
  split; [lia|]. split; [exact Hfalse|]. split.
  - intros E. discriminate.
  - split.
    + intros a b Hal Hab HaHp _. exact (Htrue a b Hal Hab HaHp).
    + split; [applys_eq Hend; lia|]. split; intros E; discriminate.
Qed.

End K5Phase.
