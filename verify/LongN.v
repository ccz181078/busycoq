From BusyCoq Require Import Individual62.

Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Inductive sideRLs_n: TM->(list (DH0*DH0))->side->nat->Prop :=
| sideRLs_n_S tm r r0 hR hL hs n0 n1:
    sideRL tm hR hL r r0 ->
    sideRLs_n tm hs r0 n0 ->
    n1<=n0 ->
    sideRLs_n tm ((hR,hL)::hs) r n1
| sideRLs_n_S' tm r hR hL hs n0:
    (forall l, exists c n, l {{{ (hR,R) }}} r -[ tm ]->> n / c /\ n0<=n) ->
    sideRLs_n tm ((hR,hL)::hs) r n0
| sideRLs_n_O' tm r:
    sideRLs_n tm [] r 0.

Local Hint Constructors sideRLs sideRLs_n: core.

Definition segRLs_n tm h1 h2 w1 w2 n :=
  (forall r1 n0,
  sideRLs_n tm h2 r1 n0 ->
  sideRLs_n tm h1 (w1*>r1) (n+n0)) /\
  (forall r1 r2,
  sideRLs tm h2 r1 r2 ->
  sideRLs tm h1 (w1*>r1) (w2*>r2)).

Lemma sideRLs_n_0 tm h r:
  sideRLs_n tm h r 0.
Proof.
  destruct h as [|[] h]; eauto.
Qed.

Lemma sideRLs_n_mono tm h r1 n n0:
  sideRLs_n tm h r1 n ->
  n0<=n ->
  sideRLs_n tm h r1 n0.
Proof.
  gen n n0 r1.
  induction h; intros; inverts H.
  - replace n0 with O by lia.
    eauto.
  - econstructor 1; eauto 1.
    lia.
  - econstructor 2.
    intros.
    specialize (H6 l).
    destruct H6 as [c [n1 [I1 I2]]].
    do 3 eexists; eauto; lia.
Qed.

Lemma segRLs_n_concat tm h1 h2 h3 w1 w2 w3 w4 n1 n2 n3:
  segRLs_n tm h1 h2 w1 w2 n1 ->
  segRLs_n tm h2 h3 w3 w4 n2 ->
  n3<=n1+n2 ->
  segRLs_n tm h1 h3 (w1++w3) (w2++w4) n3.
Proof.
  unfold segRLs_n.
  intros [Ha Hb] [Hc Hd] H.
  split; intros;
  repeat rewrite Str_app_assoc.
  - eapply sideRLs_n_mono with (n:=n1+(n2+n0)).
    2: lia.
    eauto.
  - eauto.
Qed.

Lemma segRLs_n_concat' tm h1 h2 h3 w1 w2 w3 w4 n1 n2:
  segRLs_n tm h1 h2 w1 w2 n1 ->
  segRLs_n tm h2 h3 w3 w4 n2 ->
  segRLs_n tm h1 h3 (w1++w3) (w2++w4) (n1+n2).
Proof.
  intros.
  eapply segRLs_n_concat; eauto; lia.
Qed.

Lemma sideRLs_n_split tm h1 h2 r1 n:
  sideRLs_n tm (h1++h2) r1 n ->
  sideRLs_n tm h1 r1 n \/
  (exists r2,
  sideRLs tm h1 r1 r2 /\
  sideRLs_n tm h2 r2 n).
Proof.
  gen h2 r1 n.
  induction h1; intros.
  - eauto.
  - inverts H.
    + apply IHh1 in H4.
      destruct H4 as [I1|[r2 [I1 I2]]];
      eauto 6 using sideRLs_n_mono.
    + eauto.
Qed.

Lemma sideRLs_n_trans_1 tm h1 h2 r1 n:
  sideRLs_n tm h1 r1 n ->
  sideRLs_n tm (h1++h2) r1 n.
Proof.
  intros.
  induction H; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - eapply sideRLs_n_0.
Qed.

Lemma sideRLs_n_trans_2 tm h1 h2 r1 r2 n:
  sideRLs tm h1 r1 r2 ->
  sideRLs_n tm h2 r2 n ->
  sideRLs_n tm (h1++h2) r1 n.
Proof.
  intros.
  induction H; intros.
  - eauto.
  - econstructor 1; eauto.
Qed.

Lemma segRLs_n_trans tm h1 h2 h3 h4 w1 w2 w3 n1 n2 n3:
  segRLs_n tm h1 h2 w1 w2 n1 ->
  segRLs_n tm h3 h4 w2 w3 n2 ->
  n3<=n1 ->
  n3<=n2 ->
  segRLs_n tm (h1++h3) (h2++h4) w1 w3 n3.
Proof.
  unfold segRLs_n.
  intros [Ha Hb] [Hc Hd] Hn1 Hn2.
  intros.
  split; intros.
  - eapply sideRLs_n_split in H.
    destruct H as [I1|[r2 [I1 I2]]].
    + eapply sideRLs_n_trans_1.
      eapply sideRLs_n_mono; eauto; lia.
    + eapply sideRLs_n_trans_2; eauto.
      eapply sideRLs_n_mono; eauto; lia.
  - eapply sideRLs_split in H.
    destruct H as [r3 [I1 I2]].
    eapply sideRLs_trans; eauto.
Qed.

Lemma segRLs_n_trans' tm h1 h2 h3 h4 w1 w2 w3 n1 n2:
  segRLs_n tm h1 h2 w1 w2 n1 ->
  segRLs_n tm h3 h4 w2 w3 n2 ->
  segRLs_n tm (h1++h3) (h2++h4) w1 w3 (Nat.min n1 n2).
Proof.
  intros.
  eapply segRLs_n_trans; eauto; lia.
Qed.

Lemma segRLs_n_sideRLs_n tm h1 h2 w1 w2 n r:
  segRLs_n tm h1 h2 w1 w2 n ->
  sideRLs_n tm h1 (w1*>r) n.
Proof.
  unfold segRLs_n.
  intros [Ha Hb].
  replace n with (n+0) by lia.
  eauto using sideRLs_n_0.
Qed.

Lemma sideRLs_n_sideRLs_concat tm h1 h2 ls ls' l1 l2 r1 n:
  lcons h1 ls = (ls',h2) ->
  n<=length ls' ->
  sideRLs (flip tm) ls l1 l2 ->
  sideRLs_n tm ls' r1 n ->
  exists c,
  l1 {{{ (h1,R) }}} r1 -[ tm ]->> n / c.
Proof.
  gen h1 h2 ls' l1 l2 r1 n.
  induction ls; intros.
  - inverts H.
    inverts H1.
    cbn in H0.
    replace n with O by lia.
    eauto.
  - cbn in H.
    destruct a as [a0 a1].
    destruct (lcons a1 ls) as [a2 a3] eqn:E.
    inverts H.
    cbn in H0.
    inverts H1.
    destruct n.
    1: eauto.
    inverts H2.
    + eapply sideRLs_n_mono with (n0:=n) in H10.
      2: lia.
      eapply IHls in E.
      3: apply H8.
      3: apply H10.
      2: lia.
      destruct E as [c E].
      specialize (H5 l1).
      specialize (H7 r0).
      eapply unflip_progress in H7.
      destruct a0,a1.
      cbn in H7.
      eassert (I1:_) by (eapply progress_trans; [eapply H5|eapply H7]).
      eapply progress_multistep in I1.
      destruct I1 as [n1 I1].
      eassert (I2:_) by (eapply multistep_trans; [eapply I1|eapply E]).
      replace (S n1+n) with (S n+n1) in I2 by lia.
      eapply rewind_split in I2.
      destruct I2 as [c' [I2 I3]].
      eauto.
    + specialize (H9 l1).
      destruct H9 as [c [n0 [I1 I2]]].
      replace n0 with (S n+(n0-S n)) in I1 by lia.
      eapply rewind_split in I1.
      destruct I1 as [c' [I3 I4]].
      eauto.
Qed.

Lemma sideRLs_n_sideRLs_concat_1 tm h1 h2 m l1 l2 r1 n:
  n<=m ->
  sideRLs (flip tm) ([(h2,h1)]^^m) l1 l2 ->
  sideRLs_n tm ([(h1,h2)]^^m) r1 n ->
  exists c,
  l1 {{{ (h1,R) }}} r1 -[ tm ]->> n / c.
Proof.
  intros.
  eapply sideRLs_n_sideRLs_concat with (h2:=h1); eauto.
  - clear.
    induction m; cbn; trivial.
    rewrite IHm; trivial.
  - rewrite lpow_length; cbn; lia.
Qed.

Definition segRR'(tm:TM)(h1 h2:DH0)(w1 w2:list Sym):Prop :=
  forall l r,
  l {{{ (h1,R) }}} w1 *> r -[ tm ]->+
  l <* w2 {{{ (h2,R) }}} r.

Lemma segRLs_n_S tm hR hL w1 w2:
  segRL tm hR hL w1 w2 ->
  segRLs_n tm [(hR,hL)] [] w1 w2 1.
Proof.
  unfold segRLs_n.
  intros; split; intros.
  - inverts H0.
    econstructor 2.
    intros.
    specialize (H l r1).
    eapply progress_multistep in H.
    destruct H as [n H].
    do 3 eexists; eauto; lia.
  - inverts H0.
    econstructor.
    2: econstructor.
    intro.
    eapply H.
Qed.

Lemma segRR'_segRR tm h1 h2 w1 w2:
  segRR' tm h1 h2 w1 w2 ->
  segRR tm h1 h2 w1 w2.
Proof.
  unfold segRR',segRR.
  intros.
  eapply progress_evstep; eauto.
Qed.

Lemma segLRs_sideRLs_n_concat tm ls2 w3 w4 h3 h4 r1 n0:
  segLRs tm ls2 w3 w4 ->
  sideRLs_n tm (lrcons h3 ls2 h4) r1 n0 ->
  forall l, exists c n, l <* w3 {{{ (h3,R) }}} r1 -[ tm ]->> n / c /\ n0<=n.
Proof.
  gen w3 w4 h3 h4 r1 n0.
  induction ls2; intros.
  - inverts H0.
    + inverts H8.
      replace n0 with O by lia.
      eauto.
    + inverts H.
      eauto.
  - inverts H.
    inverts H0.
    + specialize (H4 l r0).
      specialize (H5 (l<*w3)).
      eapply progress_evstep in H5.
      eassert (I1:_) by (eapply evstep_trans; [eapply H5|eapply H4]).
      eapply with_counter in I1.
      destruct I1 as [n I1].
      eapply IHls2 in H9; eauto.
      destruct H9 as [c [n2 [I2 I3]]].
      do 3 eexists.
      * eapply multistep_trans; eauto.
      * lia.
    + eauto.
Qed.

Lemma segRLs_n_lrcons tm ls2 w1 w2 w3 w4 h1 h2 h3 h4:
  segRR' tm h1 h3 w1 w3 ->
  segLL tm h4 h2 w4 w2 ->
  segLRs tm ls2 w3 w4 ->
  segRLs_n tm [(h1, h2)] (lrcons h3 ls2 h4) w1 w2 1.
Proof.
  intros.
  unfold segRLs_n; split.
  2:{
    intros.
    eapply segRLs_sideRLs_concat; eauto.
    rewrite <-(app_nil_r (lrcons _ _ _)).
    eapply segRLs_lrcons with (ls3:=[]) (ls4:=[]); eauto.
    - eapply segRR'_segRR; eauto.
    - econstructor.
  }
  intros.
  econstructor 2.
  intros.
  specialize (H l r1).
  apply progress_multistep in H.
  destruct H as [n H].
  eapply segLRs_sideRLs_n_concat in H2; eauto.
  destruct H2 as [c [n1 [I1 I2]]].
  do 3 eexists.
  - eapply multistep_trans; eauto.
  - lia.
Qed.

Lemma segRLs_n_lrcons_1 tm w1 w2 w3 h1 h2 h3 h4:
  segRR' tm h1 h3 w1 w3 ->
  segLL tm h4 h2 w3 w2 ->
  segRLs_n tm [(h1, h2)] [(h3,h4)] w1 w2 1.
Proof.
  intros.
  eapply segRLs_n_lrcons with (ls2:=[]); eauto.
  econstructor.
Qed.

Lemma segRLs_n_lrcons_2 tm w1 w2 w3 w4 h1 h2 h3 h4 h5 h6:
  segRR' tm h1 h3 w1 w3 ->
  segLR tm h4 h5 w3 w4 ->
  segLL tm h6 h2 w4 w2 ->
  segRLs_n tm [(h1, h2)] [(h3,h4);(h5,h6)] w1 w2 1.
Proof.
  intros.
  eapply segRLs_n_lrcons with (ls2:=[(h4,h5)]); eauto.
  econstructor; eauto.
  econstructor.
Qed.

Lemma segRLs_n_wall tm h1 h2 w n v1:
  segRLs_n tm h1 h2 w w v1 ->
  n<>O ->
  segRLs_n tm (h1^^n) (h2^^n) w w v1.
Proof.
  intros.
  induction n.
  1: lia.
  destruct n.
  - cbn; repeat rewrite app_nil_r.
    apply H.
  - cbn.
    eapply segRLs_n_trans; eauto.
Qed.

Ltac segRLs_n_S :=
  eapply segRLs_n_S; unfold segRR';
  solve_seg.

Ltac segRLs_n_lrcons_1 :=
  eapply segRLs_n_lrcons_1; unfold segRR';
  [solve_seg|];
  solve_seg.

Ltac segRLs_n_lrcons_2 :=
  eapply segRLs_n_lrcons_2; unfold segRR';
  [solve_seg| |];
  [solve_seg|];
  solve_seg.

Ltac solve_segRLs_n :=
  segRLs_n_S ||
  segRLs_n_lrcons_1 ||
  segRLs_n_lrcons_2 ||
  fail.

Lemma step_unbounded_nonhalt tm c:
  (forall n, exists c', c -[ tm ]->> n / c') ->
  ~halts tm c.
Proof.
  apply nonhalt_iff.
Qed.


Lemma segRLs_to_segRLs_n_0 tm h1 h2 w1 w2:
  segRLs tm h1 h2 w1 w2 ->
  segRLs_n tm h1 h2 w1 w2 0.
Proof.
  intro H.
  induction H; split; intros.
  - inverts H.
    constructor.
  - eapply segRLs_sideRLs_concat; eauto.
    constructor.
  - cbn.
    econstructor 1.
    + intros l. apply H.
    + destruct IHsegRLs as [IHn _].
      apply IHn. exact H1.
    + lia.
  - eapply segRLs_sideRLs_concat; eauto.
    econstructor; eauto.
  - cbn.
    eapply sideRLs_n_split in H3.
    destruct H3 as [I1|[r2 [I1 I2]]].
    + econstructor 2.
      intros l.
      specialize (H l r1).
      apply with_counter in H.
      destruct H as [n1 H].
      eapply segLRs_sideRLs_n_concat in I1; eauto.
      destruct I1 as [c [n2 [I2 I3]]].
      do 3 eexists.
      * eapply multistep_trans; eauto.
      * lia.
    + econstructor 1.
      * intros l.
        follow H.
        eapply progress_evstep_trans.
        2: apply H0.
        eapply sideRLs_segLRs_concat; eauto.
      * destruct IHsegRLs as [IHn _].
        apply IHn. exact I2.
      * lia.
  - eapply segRLs_sideRLs_concat; eauto.
    eapply segRLs_lrcons; eauto.
Qed.
Arguments segRLs_to_segRLs_n_0 {tm h1 h2 w1 w2} _.


