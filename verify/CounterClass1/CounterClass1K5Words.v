Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Words
  BusyCoq.CounterClass1.CounterClass1K5Common.
Require Import Lia List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Lemma k5_scan_next_rdrops P kind runs B H S D k:
  K5ScanStart P kind runs B H S D k -> K4HeadBits kind B ->
  k4_rdrops (k4_extend B (D+2) (2*S+k+4)) (2*H+k+7)=
    k4_next_k kind k.
Proof.
  intros HS HB.
  unfold K5ScanStart in HS.
  destruct HS as [Hshape [Hbits [Hhead Hpayload]]].
  unfold K5ScanPayload in Hpayload.
  destruct Hpayload as [_ [Hdrop Hrest]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk Hs]]]]]]].
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  assert (HBlast:nth H B false=true).
  { eapply k5_bits_last_true; [exact Hshape0|exact Hbits|lia]. }
  assert (Hfull:k4_rdrops (k4_extend B (D+2) (2*S+k+4))
      (length B+(D+2)+(2*S+k+4))=
      Datatypes.S (k4_rdrops (map negb B) H)).
  { replace H with (length B-1) by lia.
    apply k4_rdrops_extend_full.
    - lia.
    - replace (length B-1) with H by lia. exact HBlast.
    - lia.
    - lia. }
  destruct kind; cbn [K4HeadBits k4_next_k] in *;
    destruct HB as [B0 [B1 B2]].
  - assert (Hneg:k4_rdrops (map negb B) H=k).
    { pose proof (k4_rdrops_negb_balance B H ltac:(lia)) as E.
      rewrite B0,HBlast in E. cbn in E. lia. }
    rewrite Hneg in Hfull.
    replace (2*H+k+7) with (length B+(D+2)+(2*S+k+4)) by lia.
    replace (k+1) with (Datatypes.S k) by lia.
    exact Hfull.
  - assert (Hneg:k4_rdrops (map negb B) H=k+1).
    { pose proof (k4_rdrops_negb_balance B H ltac:(lia)) as E.
      rewrite B0,HBlast in E. cbn in E. lia. }
    rewrite Hneg in Hfull.
    replace (2*H+k+7) with (length B+(D+2)+(2*S+k+4)) by lia.
    replace (k+2) with (Datatypes.S (k+1)) by lia.
    exact Hfull.
Qed.

Lemma k5_scan_next_word P kind runs B H S D k:
  K5ScanStart P kind runs B H S D k -> K4HeadBits kind B ->
  let runsp:=runs++[D+2;1;2*S+k+4] in
  let Bp:=k4_extend B (D+2) (2*S+k+4) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+4 in
  let Dp:=2*D-k-1 in
  let kp:=k4_next_k kind k in
  K5RunShape (k4_next_kind kind) runsp Hp Sp Dp kp /\
  Bp=k4_bits (k4_first_bit (k4_next_kind kind)) runsp /\
  hd 0 runsp=1 /\ K4HeadBits (k4_next_kind kind) Bp /\
  k4_rdrops Bp Hp=kp.
Proof.
  intros HS HB. cbv zeta.
  unfold K5ScanStart in HS.
  destruct HS as [Hshape [Hbits [Hhead Hpayload]]].
  pose proof Hshape as Hshape0.
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk Hs]]]]]]].
  assert (Hlen:3<=length B) by
    (rewrite Hbits,k4_bits_length,Hsum; lia).
  split; [exact (k5_run_shape_next kind runs H S D k Hshape0)|].
  split; [exact (k5_extend_bits kind runs B H S D k Hshape0 Hbits)|].
  split; [exact (k5_extend_head runs B H S D k kind Hshape0 Hbits Hhead)|].
  split; [exact (k4_extend_head_bits kind B (D+2) (2*S+k+4) Hlen HB)|].
  exact (k5_scan_next_rdrops P kind runs B H S D k
    (conj Hshape0 (conj Hbits (conj Hhead Hpayload))) HB).
Qed.

Lemma k5_scan_next_middle_true P kind runs B H S D k z:
  K5ScanStart P kind runs B H S D k ->
  H+1<=z<H+D+3 ->
  nth z (k4_extend B (D+2) (2*S+k+4)) false=true.
Proof.
  intros HS Hz. apply k4_extend_middle_true.
  unfold K5ScanStart in HS.
  destruct HS as [[_ [_ [Hsum _]]] [Hbits _]].
  rewrite Hbits,k4_bits_length,Hsum. lia.
Qed.

Lemma k5_scan_next_last_true P kind runs B H S D k:
  K5ScanStart P kind runs B H S D k ->
  nth (2*H+k+7) (k4_extend B (D+2) (2*S+k+4)) false=true.
Proof.
  intros HS.
  replace (2*H+k+7) with
    (length (k4_extend B (D+2) (2*S+k+4))-1).
  - apply k4_extend_last_true. lia.
  - unfold K5ScanStart in HS.
    destruct HS as [[_ [_ [Hsum [_ [Hhs _]]]]] [Hbits _]].
    rewrite k4_extend_length,Hbits,k4_bits_length,Hsum. lia.
Qed.
