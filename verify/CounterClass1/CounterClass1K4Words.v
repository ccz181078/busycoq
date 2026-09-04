Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

Definition k4_bool_nat (b: bool) : nat := if b then 1 else 0.

Lemma k4_nth_map_negb B p:
  p<length B -> nth p (map negb B) false=negb (nth p B false).
Proof.
  intros Hp.
  rewrite (nth_indep (map negb B) (n:=p) false true);
    [exact (map_nth negb B false p)|].
  rewrite length_map. exact Hp.
Qed.

Lemma k4_rdrops_negb_balance B p:
  p<length B ->
  k4_rdrops (map negb B) p+k4_bool_nat (nth 0 B false)=
  k4_rdrops B p+k4_bool_nat (nth p B false).
Proof.
  induction p as [|p IH]; intros Hp.
  - cbn [k4_rdrops]. lia.
  - cbn [k4_rdrops].
    rewrite (k4_nth_map_negb B p ltac:(lia)).
    rewrite (k4_nth_map_negb B (S p) Hp).
    specialize (IH ltac:(lia)).
    destruct (nth p B false), (nth (S p) B false); cbn in *; lia.
Qed.

Lemma k4_rdrops_prefix X Y p:
  S p<=length X -> k4_rdrops (X++Y) p=k4_rdrops X p.
Proof.
  induction p as [|p IH]; intros Hp; cbn [k4_rdrops].
  - reflexivity.
  - rewrite !app_nth1 by lia. rewrite IH by lia. reflexivity.
Qed.

Lemma k4_rdrops_advance_no_drop B p n:
  (forall i, i<n ->
    (if nth (p+i) B false && negb (nth (S (p+i)) B false)
     then 1 else 0)=0) ->
  k4_rdrops B (p+n)=k4_rdrops B p.
Proof.
  induction n as [|n IH]; intros Hnone.
  - replace (p+0) with p by lia. reflexivity.
  - replace (p+S n) with (S (p+n)) by lia.
    cbn [k4_rdrops]. rewrite Hnone by lia. rewrite IH; [lia|].
    intros i Hi. apply Hnone. lia.
Qed.

Lemma k4_rdrops_advance_drop B p:
  nth p B false=true -> nth (S p) B false=false ->
  k4_rdrops B (S p)=S (k4_rdrops B p).
Proof.
  intros Hp HSp. cbn [k4_rdrops]. rewrite Hp,HSp. cbn. lia.
Qed.

Lemma k4_extend_bits kind runs B H S D k:
  K4RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs ->
  k4_extend B (D+3) (2*S+k+3) =
  k4_bits (k4_first_bit (k4_next_kind kind))
    (runs++[D+3; 1; 2*S+k+3]).
Proof.
  intros [_ [Hcount _]] ->.
  unfold k4_extend.
  rewrite k4_bits_app.
  destruct kind; cbn in *.
  - rewrite k4_bits_negb.
    rewrite (k4_after_odd k false runs); [|lia].
    cbn [k4_bits]. rewrite ?app_nil_r. reflexivity.
  - rewrite k4_bits_negb.
    rewrite (k4_after_even (k+1) true runs); [|lia].
    cbn [k4_bits]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma k4_extend_head_bits kind B L T:
  3<=length B -> K4HeadBits kind B ->
  K4HeadBits (k4_next_kind kind) (k4_extend B L T).
Proof.
  intros Hlen HB.
  destruct kind; cbn in HB |- *; destruct HB as [B0 [B1 B2]].
  - repeat split; rewrite k4_extend_old; try lia;
      rewrite ?B0, ?B1, ?B2; reflexivity.
  - repeat split; rewrite k4_extend_old; try lia;
      rewrite ?B0, ?B1, ?B2; reflexivity.
Qed.

Lemma k4_extend_head runs B H S D k kind:
  K4RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs -> hd 0 runs=1 ->
  hd 0 (runs++[D+3; 1; 2*S+k+3])=1.
Proof.
  intros [Hpos [Hcount _]] HB Hhead.
  destruct runs; cbn in *; congruence.
Qed.

Lemma k4_bits_last_true kind runs B H S D k a:
  K4RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs ->
  H+1-S<=a<H+1 -> nth a B false=true.
Proof.
  intros [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk HS]]]]]]]
    -> Ha.
  assert (Hne: runs<>[]) by
    (intros ->; destruct kind; cbn in Hcount; lia).
  set (pre:=removelast runs).
  assert (Hsplit: runs=pre++[S]).
  { unfold pre. rewrite <- Hlast. apply app_removelast_last. exact Hne. }
  assert (Hprelen: length pre=
      match kind with K4T4 => 2*k | K4T2 => 2*k+1 end).
  { rewrite Hsplit, length_app in Hcount. destruct kind; cbn in *; lia. }
  assert (Hpresum: k4_sum pre=H+1-S).
  { rewrite Hsplit, k4_sum_app in Hsum. cbn in Hsum. lia. }
  rewrite Hsplit, k4_bits_app.
  assert (Hafter: k4_after (k4_first_bit kind) pre=true).
  { destruct kind; cbn in *.
    - apply k4_after_even with (k:=k). exact Hprelen.
    - apply k4_after_odd with (k:=k). exact Hprelen. }
  rewrite Hafter. cbn [k4_bits]. rewrite app_nil_r.
  rewrite app_nth2; [|rewrite k4_bits_length,Hpresum; lia].
  rewrite k4_bits_length,Hpresum,nth_repeat_lt; lia.
Qed.

Lemma k4_extend_suffix_true B L T a:
  length B+L+1<=a<length B+L+1+T ->
  nth a (k4_extend B L T) false=true.
Proof.
  intros Ha. unfold k4_extend.
  rewrite app_nth2; [|rewrite length_map; lia].
  rewrite length_map.
  rewrite app_nth2; [|rewrite repeat_length; lia].
  rewrite repeat_length.
  replace (a-length B-L) with (S (a-length B-L-1)) by lia. cbn.
  rewrite nth_repeat_lt; lia.
Qed.

Lemma k4_extend_last_true B L T:
  0<T -> nth (length (k4_extend B L T)-1)
    (k4_extend B L T) false=true.
Proof.
  intros HT. apply k4_extend_suffix_true.
  rewrite k4_extend_length. lia.
Qed.

Lemma k4_extend_middle_true B L T a:
  length B<=a<length B+L ->
  nth a (k4_extend B L T) false=true.
Proof.
  intros Ha. unfold k4_extend.
  rewrite app_nth2; [|rewrite length_map; lia].
  rewrite length_map.
  rewrite app_nth1; [|rewrite repeat_length; lia].
  rewrite nth_repeat_lt; lia.
Qed.

Lemma k4_extend_separator_false B L T:
  nth (length B+L) (k4_extend B L T) false=false.
Proof.
  unfold k4_extend.
  rewrite app_nth2; [|rewrite length_map; lia].
  rewrite length_map.
  rewrite app_nth2; [|rewrite repeat_length; lia].
  rewrite repeat_length. replace (length B+L-length B-L) with 0 by lia.
  reflexivity.
Qed.

Lemma k4_rdrops_extend_full B L T:
  0<length B -> nth (length B-1) B false=true -> 0<L -> 0<T ->
  k4_rdrops (k4_extend B L T) (length B+L+T)=
  S (k4_rdrops (map negb B) (length B-1)).
Proof.
  intros HBlen HBlast HL HT.
  set (p0:=length B-1).
  fold p0 in HBlast.
  assert (Hp0: p0<length B) by (unfold p0; lia).
  assert (Hprefix: k4_rdrops (k4_extend B L T) p0=
      k4_rdrops (map negb B) p0).
  { unfold k4_extend. apply k4_rdrops_prefix. rewrite length_map. lia. }
  assert (Hmiddle: k4_rdrops (k4_extend B L T) (p0+L)=
      k4_rdrops (k4_extend B L T) p0).
  { apply k4_rdrops_advance_no_drop. intros i Hi.
    destruct i as [|i].
    - replace (p0+0) with p0 by lia.
      replace (S p0) with (length B) by (unfold p0; lia).
      rewrite k4_extend_old by exact Hp0. rewrite HBlast.
      rewrite k4_extend_middle_true by lia. reflexivity.
    - rewrite (k4_extend_middle_true B L T (p0+S i)) by
        (unfold p0; lia).
      rewrite (k4_extend_middle_true B L T (S (p0+S i))) by
        (unfold p0; lia).
      reflexivity. }
  assert (Hdrop: k4_rdrops (k4_extend B L T) (S (p0+L))=
      S (k4_rdrops (k4_extend B L T) (p0+L))).
  { apply k4_rdrops_advance_drop.
    - rewrite k4_extend_middle_true; [reflexivity|unfold p0; lia].
    - replace (S (p0+L)) with (length B+L) by (unfold p0; lia).
      apply k4_extend_separator_false. }
  assert (Htail: k4_rdrops (k4_extend B L T) (S (p0+L)+T)=
      k4_rdrops (k4_extend B L T) (S (p0+L))).
  { apply k4_rdrops_advance_no_drop. intros i Hi.
    destruct i as [|i].
    - replace (S (p0+L)+0) with (length B+L) by (unfold p0; lia).
      rewrite k4_extend_separator_false.
      rewrite k4_extend_suffix_true by lia. reflexivity.
    - rewrite (k4_extend_suffix_true B L T (S (p0+L)+S i)) by
        (unfold p0; lia).
      rewrite (k4_extend_suffix_true B L T (S (S (p0+L)+S i))) by
        (unfold p0; lia).
      reflexivity. }
  replace (length B+L+T) with (S (p0+L)+T) by (unfold p0; lia).
  rewrite Htail,Hdrop,Hmiddle,Hprefix. reflexivity.
Qed.

Lemma k4_scan_start_rdrops_full P kind runs B H S D k:
  K4ScanStart P kind runs B H S D k -> k4_rdrops B H=k.
Proof.
  unfold K4ScanStart. destruct kind; cbn.
  all: intros [HS [HB [Hhead [Hbase [Hdrop Hrest]]]]];
    pose proof HS as HS0;
    destruct HS as [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk Hs]]]]]]].
  - assert (Hsame: k4_rdrops B ((H-2)+(H-(H-2)))=k4_rdrops B (H-2)).
    { apply k4_rdrops_advance_no_drop. intros i Hi.
      assert (Bi: nth (H-2+i) B false=true).
      { eapply k4_bits_last_true; [exact HS0|exact HB|lia]. }
      assert (Bi1: nth (Datatypes.S (H-2+i)) B false=true).
      { eapply k4_bits_last_true; [exact HS0|exact HB|lia]. }
      rewrite Bi,Bi1. reflexivity. }
    replace ((H-2)+(H-(H-2))) with H in Hsame by lia.
    rewrite Hsame. replace (H-2) with (H-6+4) by lia. exact Hdrop.
  - assert (Hsame: k4_rdrops B ((H-1)+(H-(H-1)))=k4_rdrops B (H-1)).
    { apply k4_rdrops_advance_no_drop. intros i Hi.
      assert (Bi: nth (H-1+i) B false=true).
      { eapply k4_bits_last_true; [exact HS0|exact HB|lia]. }
      assert (Bi1: nth (Datatypes.S (H-1+i)) B false=true).
      { eapply k4_bits_last_true; [exact HS0|exact HB|lia]. }
      rewrite Bi,Bi1. reflexivity. }
    replace ((H-1)+(H-(H-1))) with H in Hsame by lia.
    rewrite Hsame. replace (H-1) with (H-5+4) by lia. exact Hdrop.
Qed.

Lemma k4_scan_next_rdrops P kind runs B H S D k:
  K4ScanStart P kind runs B H S D k -> K4HeadBits kind B ->
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  k4_rdrops (k4_extend B (D+3) Sp)
    (Hp-k4_gap (k4_next_kind kind)+4)=k4_next_k kind k.
Proof.
  intros HS HB.
  pose proof HS as HS0.
  unfold K4ScanStart in HS0.
  destruct kind; cbn in HB |- *.
  all: destruct HS0 as [Hshape [Hbits Hrest]];
    pose proof Hshape as Hshape0;
    destruct Hshape as [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk Hs]]]]]]];
    assert (Hlen: length B=H+1) by
      (rewrite Hbits,k4_bits_length,Hsum; reflexivity);
    assert (HBlast: nth H B false=true) by
      (eapply k4_bits_last_true; [exact Hshape0|exact Hbits|lia]);
    pose proof (k4_scan_start_rdrops_full P _ runs B H S D k HS) as Hdrop.
  - destruct HB as [B0 [B1 B2]].
    assert (Hneg: k4_rdrops (map negb B) H=k).
    { pose proof (k4_rdrops_negb_balance B H ltac:(lia)) as E.
      rewrite B0,HBlast in E. cbn in E. lia. }
    assert (Hfull: k4_rdrops (k4_extend B (D+3) (2*S+k+3))
        (length B+(D+3)+(2*S+k+3))=Datatypes.S k).
    { pose proof (k4_rdrops_extend_full B (D+3) (2*S+k+3)
        ltac:(lia) ltac:(replace (length B-1) with H by lia; exact HBlast)
        ltac:(lia) ltac:(lia)) as E.
      replace (length B-1) with H in E by lia. rewrite Hneg in E. exact E. }
    assert (Hsame: k4_rdrops (k4_extend B (D+3) (2*S+k+3))
        ((2*H+k+7-5+4)+1)=
        k4_rdrops (k4_extend B (D+3) (2*S+k+3))
          (2*H+k+7-5+4)).
    { apply k4_rdrops_advance_no_drop. intros i Hi.
      assert (i=0) by lia. subst i.
      replace (2*H+k+7-5+4+0) with (2*H+k+7-5+4) by lia.
      rewrite (k4_extend_suffix_true B (D+3) (2*S+k+3)
        (2*H+k+7-5+4)) by (rewrite Hlen; lia).
      rewrite (k4_extend_suffix_true B (D+3) (2*S+k+3)
        (Datatypes.S (2*H+k+7-5+4))) by (rewrite Hlen; lia).
      reflexivity. }
    replace ((2*H+k+7-5+4)+1)
      with (length B+(D+3)+(2*S+k+3)) in Hsame by
      (rewrite Hlen; lia).
    rewrite Hsame in Hfull.
    replace (Datatypes.S k) with (k+1) in Hfull by lia. exact Hfull.
  - destruct HB as [B0 [B1 B2]].
    assert (Hneg: k4_rdrops (map negb B) H=k+1).
    { pose proof (k4_rdrops_negb_balance B H ltac:(lia)) as E.
      rewrite B0,HBlast in E. cbn in E. lia. }
    assert (Hfull: k4_rdrops (k4_extend B (D+3) (2*S+k+3))
        (length B+(D+3)+(2*S+k+3))=Datatypes.S (k+1)).
    { pose proof (k4_rdrops_extend_full B (D+3) (2*S+k+3)
        ltac:(lia) ltac:(replace (length B-1) with H by lia; exact HBlast)
        ltac:(lia) ltac:(lia)) as E.
      replace (length B-1) with H in E by lia. rewrite Hneg in E. exact E. }
    assert (Hsame: k4_rdrops (k4_extend B (D+3) (2*S+k+3))
        ((2*H+k+7-6+4)+2)=
        k4_rdrops (k4_extend B (D+3) (2*S+k+3))
          (2*H+k+7-6+4)).
    { apply k4_rdrops_advance_no_drop. intros i Hi.
      rewrite (k4_extend_suffix_true B (D+3) (2*S+k+3)
        (2*H+k+7-6+4+i)) by (rewrite Hlen; lia).
      rewrite (k4_extend_suffix_true B (D+3) (2*S+k+3)
        (Datatypes.S (2*H+k+7-6+4+i))) by (rewrite Hlen; lia).
      reflexivity. }
    replace ((2*H+k+7-6+4)+2)
      with (length B+(D+3)+(2*S+k+3)) in Hsame by
      (rewrite Hlen; lia).
    rewrite Hsame in Hfull.
    replace (Datatypes.S (k+1)) with (k+2) in Hfull by lia. exact Hfull.
Qed.

Lemma k4_scan_next_word P kind runs B H S D k:
  K4ScanStart P kind runs B H S D k -> K4HeadBits kind B ->
  let runsp:=runs++[D+3; 1; 2*S+k+3] in
  let Bp:=k4_extend B (D+3) (2*S+k+3) in
  let Hp:=2*H+k+7 in
  let Sp:=2*S+k+3 in
  let Dp:=2*D+1-k in
  let kp:=k4_next_k kind k in
  K4RunShape (k4_next_kind kind) runsp Hp Sp Dp kp /\
  Bp=k4_bits (k4_first_bit (k4_next_kind kind)) runsp /\
  hd 0 runsp=1 /\ K4HeadBits (k4_next_kind kind) Bp /\
  k4_rdrops Bp (Hp-k4_gap (k4_next_kind kind)+4)=kp.
Proof.
  intros HS HB. cbv zeta.
  pose proof HS as HS0.
  unfold K4ScanStart in HS0.
  destruct HS0 as [Hshape [Hbits [Hhead Hrest]]].
  assert (Hlen: 3<=length B).
  { destruct Hshape as [_ [_ [Hsum [_ [_ [Hlarge _]]]]]].
    rewrite Hbits,k4_bits_length,Hsum. lia. }
  split; [exact (k4_run_shape_next kind runs H S D k Hshape)|].
  split; [exact (k4_extend_bits kind runs B H S D k Hshape Hbits)|].
  split; [exact (k4_extend_head runs B H S D k kind Hshape Hbits Hhead)|].
  split; [exact (k4_extend_head_bits kind B (D+3) (2*S+k+3) Hlen HB)|].
  exact (k4_scan_next_rdrops P kind runs B H S D k HS HB).
Qed.

Lemma k4_scan_next_middle_window P kind runs B H S D k j:
  K4ScanStart P kind runs B H S D k -> j<=10 ->
  nth (2*D+1-k-7+j) (k4_extend B (D+3) (2*S+k+3)) false=true.
Proof.
  intros HS Hj.
  unfold K4ScanStart in HS.
  destruct HS as [Hshape [Hbits Hrest]].
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk Hs]]]]]]].
  apply k4_extend_middle_true.
  rewrite Hbits,k4_bits_length,Hsum. lia.
Qed.

Lemma k4_scan_next_last_true P kind runs B H S D k:
  K4ScanStart P kind runs B H S D k ->
  nth (2*H+k+7) (k4_extend B (D+3) (2*S+k+3)) false=true.
Proof.
  intros HS.
  unfold K4ScanStart in HS.
  destruct HS as [Hshape [Hbits Hrest]].
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk Hs]]]]]]].
  replace (2*H+k+7) with
    (length (k4_extend B (D+3) (2*S+k+3))-1).
  - apply k4_extend_last_true. lia.
  - rewrite k4_extend_length,Hbits,k4_bits_length,Hsum. lia.
Qed.
