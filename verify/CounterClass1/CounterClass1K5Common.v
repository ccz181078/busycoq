Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4Particles BusyCoq.CounterClass1.CounterClass1K4Words.
Require Import Lia.
Require Import List Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

(* Constructor interface shared verbatim by TM15 and TM16. *)
Record K5Rules (P:nat->nat->nat->nat->Prop) := {
  k5_rst01: P 1 0 0 7;
  k5_rst0: P 0 1 0 6;
  k5_inc01: forall a c d,
    P a 0 (1+c) d -> P (1+a) 0 c (4+d);
  k5_rov: forall a b c d c' d',
    P a b c (4+d) -> P c d c' d' -> P a (2+b) c' (1+d');
  k5_rov': forall a b c d c' d',
    P a b c (5+d) -> P c d (1+c') d' -> P a (2+b) c' (4+d');
  k5_lov1: forall a n,
    P a 0 0 (3+n*2) -> P (3+a) 0 n 9;
  k5_lov2: forall a n,
    P a 0 0 (1+n*2) -> P (1+a) 3 n 6;
  k5_lov2': forall a b c d n,
    P a b c (5+d) -> P c d 0 (1+n*2) -> P a (5+b) n 6;
  k5_lov3: forall a n,
    P a 0 0 (3+n*2) -> P (2+a) 2 n 9;
  k5_lov3': forall a b c d c' d' n,
    P a b c (7+d) -> P c d c' (5+d') ->
    P c' d' 0 (3+n*2) -> P a (4+b) n 9;
  k5_lov5: forall a b c d n,
    P a b c (5+d) -> P c d 0 (n*2) -> P a (7+b) (1+n) 5;
  k5_lov4: forall a b c d c' d' n,
    P a b c (6+d) -> P c d c' (5+d') ->
    P c' d' 0 (n*2) -> P a (5+b) n 6;
  k5_lov6: forall a b c d c' d' n,
    P a b c (6+d) -> P c d c' (5+d') ->
    P c' d' 0 (1+n*2) -> P a (7+b) (2+n) 5;
  k5_lov7: forall a b c d c' d' n,
    P a b c (8+d) -> P c d c' (5+d') ->
    P c' d' 0 (3+n*2) -> P a (2+b) n 8;
  k5_lov8: forall a b c d c' d' c'' d'' n,
    P a b c (7+d) -> P c d c' (6+d') ->
    P c' d' c'' (5+d'') -> P c'' d'' 0 (2+n*2) ->
    P a (4+b) n 9;
  k5_lov9: forall a b c d c' d' c0 d0 c1 d1 n c2 d2,
    P a b c (6+d) -> P c d c' (7+d') ->
    P c' d' c0 (6+d0) -> P c0 d0 c1 (5+d1) ->
    P c1 d1 0 (n*2) -> P (1+n) 0 c2 d2 ->
    P a (4+b) c2 (1+d2)
}.

Arguments k5_inc01 {P} _ _ _ _ _.
Arguments k5_rov {P} _ _ _ _ _ _ _ _ _.
Arguments k5_rov' {P} _ _ _ _ _ _ _ _ _.
Arguments k5_lov1 {P} _ _ _ _.
Arguments k5_lov2 {P} _ _ _ _.
Arguments k5_lov3 {P} _ _ _ _.

(* Subtracting one from the fourth parameter turns the K5 width invariant
   into the K4 width invariant.  More importantly, all three ordinary rules
   then become exactly the core K4 rules, so every Boolean-row and particle
   lemma can be reused without reproving its four local cases. *)
Definition K5Q (P:nat->nat->nat->nat->Prop) a b c d : Prop :=
  P a b c (1+d).

Section K5Core.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.

Definition k5_q_core_rules:K4CoreRules (K5Q P).
Proof.
  constructor; unfold K5Q; intros.
  - replace (1+(4+d)) with (4+(1+d)) by lia.
    exact (k5_inc01 R a c (1+d) H).
  - exact (k5_rov R a b c d c' (1+d') H H0).
  - replace (1+(4+d')) with (4+(1+d')) by lia.
    exact (k5_rov' R a b c d c' (1+d') H H0).
Qed.

Lemma k5_inc01_iter e q de:
  P e 0 q de -> P (e+q) 0 0 (de+4*q).
Proof.
  revert e de. induction q as [|q IH]; intros e de HE.
  - applys_eq HE; lia.
  - applys_eq (IH (S e) (de+4)); try lia.
    applys_eq (k5_inc01 R e q de); try lia.
    applys_eq HE; lia.
Qed.

(* A zero-output axis fact reproduces itself at twice the scale.  This is the
   short spine visible between consecutive major PLOv2 events. *)
Lemma k5_seed_next a:
  P a 0 0 (2*a+5) -> P (2*a+4) 0 0 (2*(2*a+4)+5).
Proof.
  intros Hseed.
  assert (Hstart:P (a+3) 0 (a+1) 9).
  { assert (Hseed':P a 0 0 (3+(a+1)*2)) by
      (applys_eq Hseed; lia).
    applys_eq (k5_lov1 R a (a+1) Hseed'); lia. }
  applys_eq (k5_inc01_iter (a+3) (a+1) 9 Hstart); lia.
Qed.

Lemma k5_seed_major a:
  P a 0 0 (2*a+5) -> P (a+1) 3 (a+2) 6.
Proof.
  intros Hseed.
  assert (Hseed':P a 0 0 (1+(a+2)*2)) by
    (applys_eq Hseed; lia).
  applys_eq (k5_lov2 R a (a+2) Hseed'); lia.
Qed.

Fixpoint k5_seed_index (n:nat) (a:nat) : nat :=
  match n with
  | 0 => a
  | S n => 2*k5_seed_index n a+4
  end.

Lemma k5_seed_iter a:
  P a 0 0 (2*a+5) -> forall n,
  P (k5_seed_index n a) 0 0 (2*k5_seed_index n a+5).
Proof.
  intros H n. induction n; cbn; [exact H|].
  exact (k5_seed_next _ IHn).
Qed.

Lemma k5_seed_index_large a n: a+n<=k5_seed_index n a.
Proof. induction n; cbn; lia. Qed.

(* The K5 word uses the same alternating-run convention as complex K4.
   Only the three appended run lengths differ.  The parameter [k] is the
   number of true-to-false boundaries, so the two possible run counts are
   exactly the existing [K4T4]/[K4T2] counts. *)
Definition K5RunShape (kind:K4Kind) (runs:list nat)
    (H S D k:nat) : Prop :=
  Forall (fun n => 0<n) runs /\
  length runs=k4_run_count kind k /\
  k4_sum runs=H+1 /\
  last runs 0=S /\
  H=2*S+D /\
  4*S+3*k+15<=H /\
  3<=k /\ 3<=S.

Lemma k5_run_shape_next kind runs H S D k:
  K5RunShape kind runs H S D k ->
  K5RunShape (k4_next_kind kind)
    (runs++[D+2;1;2*S+k+4])
    (2*H+k+7) (2*S+k+4) (2*D-k-1) (k4_next_k kind k).
Proof.
  intros [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk HS]]]]]]].
  assert (Hlast':last (runs++[D+2;1;2*S+k+4]) 0=2*S+k+4).
  { replace (runs++[D+2;1;2*S+k+4])
      with ((runs++[D+2;1])++[2*S+k+4]).
    - apply last_last.
    - symmetry.
      change (runs++([D+2;1]++[2*S+k+4])=
        (runs++[D+2;1])++[2*S+k+4]).
      apply app_assoc. }
  destruct kind; cbn [k4_run_count k4_next_kind k4_next_k] in *;
    repeat split; try lia.
  all: try (apply Forall_app; split; [exact Hpos|repeat constructor; lia]).
  all: try (rewrite length_app; cbn; lia).
  all: try (rewrite k4_sum_app; cbn; lia).
  all: try exact Hlast'.
  all: try lia.
  all: cbn [k4_run_count]; lia.
Qed.

Lemma k5_extend_bits kind runs B H S D k:
  K5RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs ->
  k4_extend B (D+2) (2*S+k+4)=
  k4_bits (k4_first_bit (k4_next_kind kind))
    (runs++[D+2;1;2*S+k+4]).
Proof.
  intros [_ [Hcount _]] ->. unfold k4_extend.
  rewrite k4_bits_app,k4_bits_negb.
  destruct kind; cbn in *.
  - rewrite (k4_after_odd k false runs) by lia.
    cbn [k4_bits]. rewrite ?app_nil_r. reflexivity.
  - rewrite (k4_after_even (k+1) true runs) by lia.
    cbn [k4_bits]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma k5_extend_head runs B H S D k kind:
  K5RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs -> hd 0 runs=1 ->
  hd 0 (runs++[D+2;1;2*S+k+4])=1.
Proof.
  intros [Hpos [Hcount _]] HB Hhead.
  destruct runs; cbn in *; congruence.
Qed.

Lemma k5_bits_last_true kind runs B H S D k a:
  K5RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs ->
  H+1-S<=a<H+1 -> nth a B false=true.
Proof.
  intros [Hpos [Hcount [Hsum [Hlast Hrest]]]] -> Ha.
  assert (Hne:runs<>[]) by
    (intros ->; destruct kind; cbn in Hcount; lia).
  set (pre:=removelast runs).
  assert (Hsplit:runs=pre++[S]).
  { unfold pre. rewrite <-Hlast. apply app_removelast_last. exact Hne. }
  assert (Hprelen:length pre=
      match kind with K4T4 => 2*k | K4T2 => 2*k+1 end).
  { rewrite Hsplit,length_app in Hcount. destruct kind; cbn in *; lia. }
  assert (Hpresum:k4_sum pre=H+1-S).
  { rewrite Hsplit,k4_sum_app in Hsum. cbn in Hsum. lia. }
  rewrite Hsplit,k4_bits_app.
  assert (Hafter:k4_after (k4_first_bit kind) pre=true).
  { destruct kind; cbn in *.
    - apply k4_after_even with (k:=k). exact Hprelen.
    - apply k4_after_odd with (k:=k). exact Hprelen. }
  rewrite Hafter. cbn [k4_bits]. rewrite app_nil_r,app_nth2;
    [|rewrite k4_bits_length,Hpresum; lia].
  rewrite k4_bits_length,Hpresum,nth_repeat_lt; lia.
Qed.

Definition k5_scan_y (kind:K4Kind) H :=
  match kind with K4T4 => H-1 | K4T2 => H end.

Lemma k5_pointer_trace kind runs B H S D k u:
  K5RunShape kind runs H S D k ->
  B=k4_bits (k4_first_bit kind) runs ->
  (nth 0 B false=true \/ nth 1 B false=true) ->
  2*length B<=u+2 -> 2*H<=u ->
  k4_rdrops B H=k ->
  K4PointerTrace B u H (k5_scan_y kind H) (H+k).
Proof.
  intros HS HB Hbase Hlen Hu Hdrop.
  assert (HBl:length B=H+1).
  { destruct HS as [_ [_ [Hsum _]]]. rewrite HB,k4_bits_length,Hsum.
    reflexivity. }
  assert (BH:nth H B false=true).
  { eapply k5_bits_last_true; eauto. destruct HS as
      [_ [_ [_ [_ [_ [_ [_ HT]]]]]]]. lia. }
  destruct kind; cbn [k5_scan_y] in *.
  - assert (HH:2<=H) by
      (destruct HS as [_ [_ [_ [_ [Hhs [_ [_ HT]]]]]]]; lia).
    assert (BHm:nth (H-1) B false=true).
    { eapply k5_bits_last_true; eauto. destruct HS as
        [_ [_ [_ [_ [Hhs [_ [_ HT]]]]]]]; lia. }
    assert (Hdrop':k4_rdrops B (H-1)=k).
    { replace H with (Datatypes.S (H-1)) in Hdrop by lia.
      cbn [k4_rdrops] in Hdrop.
      replace (Datatypes.S (H-1)) with H in Hdrop by lia.
      rewrite BHm,BH in Hdrop. cbn in Hdrop.
      lia. }
    destruct (k4_pointer_scan B Hbase (H-1)) as [Hscan _].
    replace (H+k) with (Datatypes.S ((H-1)+k)) by lia.
    apply K4PointerMore.
    + rewrite HBl; lia.
    + rewrite HBl; lia.
    + intros; lia.
    + intros Hfalse. rewrite BHm in Hfalse. discriminate.
    + lia.
    + lia.
    + exact Hlen.
    + lia.
    + assert (HT:K4PointerTrace B (u+2) (H-1) (H-1) ((H-1)+k)).
      { replace ((H-1)+k) with ((H-1)+k4_rdrops B (H-1)) by lia.
        apply Hscan.
        - rewrite HBl; lia.
        - lia.
        - lia. }
      unfold k4_next_x,k4_next_y. rewrite BH,BHm. cbn.
      unfold k4_next_x. rewrite BH. cbn.
      exact HT.
  - destruct (k4_pointer_scan B Hbase H) as [Hscan _].
    applys_eq (Hscan u); try rewrite HBl; try rewrite Hdrop; lia.
Qed.

Definition k5_row_false_d (kind:K4Kind) :=
  match kind with K4T4 => 20 | K4T2 => 18 end.

Definition K5Tail (P:nat->nat->nat->nat->Prop) H : Prop :=
  P (H+1) 12 H 19 /\
  P (H+2) 10 (H-1) 21 /\
  P (H+3) 8 (H-1) 21 /\
  P (H+4) 6 H 19 /\
  P (H+5) 4 (H-1) 21 /\
  P (H+6) 2 H 19.

Definition K5ScanPayload (P:nat->nat->nat->nat->Prop)
    (kind:K4Kind) (B:list bool) (H S D k:nat) : Prop :=
  K4HeadBits kind B /\
  k4_rdrops B H=k /\
  K4ExactRow (K5Q P) B true (2*H+13) H 17 /\
  K4ExactRow (K5Q P) B false (2*H+14) (k5_scan_y kind H)
    (k5_row_false_d kind) /\
  K5Tail P H /\
  P (H+7) 0 (D-5) (4*S+29).

Definition K5ScanStart (P:nat->nat->nat->nat->Prop)
    (kind:K4Kind) (runs:list nat) (B:list bool)
    (H S D k:nat) : Prop :=
  K5RunShape kind runs H S D k /\
  B=k4_bits (k4_first_bit kind) runs /\
  hd 0 runs=1 /\
  K5ScanPayload P kind B H S D k.

Definition K5FirstGen (P:nat->nat->nat->nat->Prop)
    (kind:K4Kind) (B:list bool) (H S D k:nat) : Prop :=
  let u:=2*H+13 in
  let q:=D-5 in
  let e:=H+7 in
  let A:=H+D+2 in
  let Sp:=2*S+k+4 in
  exists xg yg,
    K4PointerTrace B (u+2*(q+3)) xg yg (Sp-2) /\
    K4Row (K5Q P) B true (u+2*(q+3)) xg /\
    K4Row (K5Q P) B false (u+2*(q+3)+1) yg /\
    yg<=xg<=Datatypes.S yg /\
    (forall j, j<=q -> K4Particle (K5Q P)
      (u+2*(q+3)) (e+j) yg) /\
    P A 0 0 (2*A+5).

Lemma k5_scan_first kind runs B H S D k:
  K5ScanStart P kind runs B H S D k ->
  K5FirstGen P kind B H S D k.
Proof.
  intros HS0.
  unfold K5ScanStart,K5ScanPayload in HS0.
  destruct HS0 as [Hshape [Hbits [Hhead
    [Hheads [Hdrop [RT0 [RF0 [Htail Hex]]]]]]]].
  destruct Hshape as [Hpos [Hcount [Hsum [Hlast
    [Hhs [Hlarge [Hk HS]]]]]]] eqn:Eshape.
  assert (Hshape':K5RunShape kind runs H S D k) by
    (unfold K5RunShape; repeat split; assumption).
  assert (Hlen:length B=H+1) by
    (rewrite Hbits,k4_bits_length,Hsum; reflexivity).
  assert (Hbase:nth 0 B false=true \/ nth 1 B false=true).
  { destruct kind; cbn [K4HeadBits] in Hheads;
      destruct Hheads as [B0 [B1 B2]]; auto. }
  set (u:=2*H+13).
  set (q:=D-5).
  set (e:=H+7).
  set (A:=H+D+2).
  set (Sp:=2*S+k+4).
  assert (HT:K4PointerTrace B u H (k5_scan_y kind H) (H+k)).
  { eapply k5_pointer_trace.
    - exact Hshape'.
    - exact Hbits.
    - exact Hbase.
    - unfold u. rewrite Hlen. lia.
    - unfold u. lia.
    - exact Hdrop. }
  assert (RT:K4Row (K5Q P) B true u H) by
    (exists 17; unfold u; applys_eq RT0; lia).
  assert (RF:K4Row (K5Q P) B false (u+1) (k5_scan_y kind H)) by
    (exists (k5_row_false_d kind); unfold u; applys_eq RF0; lia).
  assert (Hq3:q+3<=H+k) by (unfold q; lia).
  destruct (k4_pointer_trace_split B u H (k5_scan_y kind H)
      (H+k) (q+3) Hq3 HT) as (xg&yg&m&Hm&HPg&HTg).
  assert (HD5:5<=D).
  { destruct kind; cbn [k4_run_count] in Hlarge; lia. }
  assert (Hm':m=Sp-2) by (unfold q,Sp in *; lia). subst m.
  destruct (k4_pointer_prefix_rows (K5Q P) k5_q_core_rules
      B u H (k5_scan_y kind H) (q+3) xg yg HPg RT RF) as [RTg RFg].
  assert (Hpair0:k5_scan_y kind H<=H<=Datatypes.S (k5_scan_y kind H)).
  { destruct kind; cbn [k5_scan_y]; lia. }
  assert (Hpairg:yg<=xg<=Datatypes.S yg).
  { eapply k4_pointer_prefix_pair; eauto. }
  assert (Hqy:q+2<=k5_scan_y kind H).
  { destruct kind; cbn [k5_scan_y]; unfold q; lia. }
  assert (Hex':K5Q P e 0 q (4*S+28)).
  { unfold K5Q,e,q. applys_eq Hex; lia. }
  assert (Hew:2*e=u+1) by (unfold e,u; lia).
  assert (Heout:2*q+(4*S+28)=u+5) by (unfold q,u; lia).
  assert (Hgen:forall j, j<=q -> K4Particle (K5Q P)
      (u+2*(q+3)) (e+j) yg).
  { intros j Hj.
    exact (k4_generated_synced (K5Q P) k5_q_core_rules B u H
      (k5_scan_y kind H) q e (4*S+28) xg yg Hbase Hpair0 Hqy
      HPg RT RF Hex' Hew Heout j Hj). }
  assert (HZ:P A 0 0 (2*A+5)).
  { applys_eq (k5_inc01_iter e q (4*S+29) Hex);
      unfold e,q,A; lia. }
  unfold K5FirstGen. fold u q e A Sp.
  exists xg,yg. repeat split; try assumption.
  all: lia.
Qed.

End K5Core.
