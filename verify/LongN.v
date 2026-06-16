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
  intros H [n [x [I1 I2]]].
  destruct (H (n+1)) as [c' I3].
  eapply rewind_split in I3.
  destruct I3 as [c'0 [I3 I4]].
  multistep_deterministic.
  inverts I4.
  inverts H1; cbn in *; congruence.
Qed.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0RD_0LC0LB_0RD1LB_1RD1RE_1RF---_0RA1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR1 := (D,@nil Sym).
Notation hR2 := (F,<[1;1]).
Notation hL := (B,@nil Sym).
Notation h1 := [(hR1,hL)].
Notation h2 := [(hR2,hL)].

Definition P1 n := segRLs_n tm (h1^^(2^n*4-2)) (h2^^(2^n*2-1)) ([1]++[0]^^(2^n*6-2)) ([0]^^(2^n*2-1)++[1;0]) (S n).
Definition P2 n := segRLs_n tm (h1^^(2^n*4-1)) (h2^^(2^n*2)) ([1]++[0]^^(2^n*6-2)) ([0]^^(2^n*2-1)) (S n).

Lemma h2s_010 n:
  n<>O ->
  segRLs_n tm (h2^^n) (h1^^(n*2)) ([0;1;0]) ([0;1;0]++[0]^^(n*2)) 1.
Proof.
  do 2 rewrite lpow_mul.
  induction n.
  1: lia.
  destruct n.
  - intros.
    solve_segRLs_n.
  - intros.
    remember (S n) as n'.
    replace (S n') with (n'+1) by lia.
    do 2 rewrite lpow_add.
    eapply segRLs_n_trans.
    + apply IHn; lia.
    + solve_segRLs_n.
    + lia.
    + lia.
Qed.

Lemma h1s_0s n m:
  n<>O ->
  m<>O ->
  segRLs_n tm (h1^^n) (h1^^n) ([0]^^m) ([0]^^m) 1.
Proof.
  intros.
  eapply segRLs_n_wall; eauto.
  destruct m; [lia|].
  solve_segRLs_n.
Qed.

Lemma h2s_10 n:
  n<>O ->
  segRLs_n tm (h2^^n) (h2^^n) [1;0] [1;0] 1.
Proof.
  intros.
  eapply segRLs_n_wall; eauto.
  solve_segRLs_n.
Qed.

Lemma h1_0s10 n:
  segRLs_n tm h1 h2 ([0]^^n++[1;0]) ([0]^^n) (S n).
Proof.
  induction n.
  - solve_segRLs_n.
  - cbn[lpow].
    rewrite <-app_assoc.
    replace (S (S n)) with (1+S n) by lia.
    eapply segRLs_n_concat'.
    2: apply IHn.
    solve_segRLs_n.
Qed.

Lemma h2_00 r:
  segRLs_n tm h2 [] ([0;0]++r) ([0;1;0]++[1]++r) 1.
Proof.
  eapply segRLs_n_S.
  solve_seg.
Qed.

Lemma lpow_add'' {A} (ls:list A) a b ls0:
  ls^^a ++ ls^^b ++ ls0 =
  ls^^(a+b) ++ ls0.
Proof.
  rewrite app_assoc,lpow_add.
  reflexivity.
Qed.

Lemma P1_S n:
  P1 n ->
  P2 n ->
  P1 (S n).
Proof.
  unfold P1,P2.
  intros HP1 HP2.
  cbn[Nat.pow].
  replace (2*2^n*4-2) with ((2^n*4-1)+(2^n*4-1)) by lia.
  replace (h2^^(2*2^n*2-1)) with (h2^^((2^n*2-1)+(2^n*2))) by flia.
  replace (2*2^n*6-2) with ((2^n*6-2)+(2+(2^n*6-2))) by lia.
  do 3 rewrite lpow_add.
  eapply segRLs_n_trans.
  - rewrite app_assoc.
    eapply segRLs_n_concat'.
    1: apply HP2.
    replace (h2^^(2^n*2-1)) with (h2^^(0+(2^n*2-1))) by flia.
    replace (h2^^(2^n*2)) with (h2^^(1+(2^n*2-1))) by flia.
    do 3 rewrite lpow_add.
    eapply segRLs_n_trans'.
    1: apply h2_00.
    eapply segRLs_n_concat'.
    1: apply h2s_010; lia.
    applys_eq HP1; flia.
  - change ([0;1;0]) with ([0]^^1++[1]++[0]^^1).
    repeat rewrite <-app_assoc.
    repeat rewrite lpow_add''.
    replace (2*2^n*2-1) with (2^n*2-1+1+(2^n*2-1)) by lia.
    rewrite (lpow_add _ (2^n*2-1+1)),<-app_assoc.
    eapply segRLs_n_concat'.
    1: eapply h1s_0s; lia.
    rewrite app_assoc.
    eapply segRLs_n_concat'.
    1: applys_eq HP2; flia.
    eapply h2s_10; lia.
  - lia.
  - lia.
Qed.

Lemma pow2_gt n:
  n<2^n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma P2_S n:
  P1 n ->
  P2 n.
Proof.
  unfold P1,P2.
  intros HP1.
  replace (2^n*4-1) with (2^n*4-2+1) by lia.
  replace (h2^^(2^n*2)) with (h2^^(2^n*2-1+1)) by flia.
  do 2 rewrite lpow_add.
  eapply segRLs_n_trans.
  - apply HP1.
  - eapply h1_0s10.
  - lia.
  - pose proof (pow2_gt n).
    lia.
Qed.

Lemma P1_n n:
  P1 n.
Proof.
  induction n; intros.
  - unfold P1.
    cbn.
    eapply segRLs_n_trans with (h1:=h1) (h2:=[]).
    1: solve_segRLs_n.
    1: solve_segRLs_n.
    all: lia.
  - eapply P1_S; eauto using P2_S.
Qed.

Notation hLR := [(hL,hR1)].

Lemma LIncs n:
  sideRLs (flip tm) (hLR^^n) (0inf<*[1]) (0inf<*[1]^^(1+n)).
Proof.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans; eauto.
    esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=0inf<*[1] {{{ (hR1,R) }}} [1] *> 0inf).
  1: esx.
  eapply step_unbounded_nonhalt.
  intros n.
  epose proof (P1_n n) as HP1.
  unfold P1 in HP1.
  eapply segRLs_n_sideRLs_n in HP1.
  eapply sideRLs_n_mono with (n0:=n) in HP1.
  2: lia.
  eapply sideRLs_n_sideRLs_concat_1 in HP1.
  2: epose proof (pow2_gt n); lia.
  2: apply LIncs.
  rewrite Str_app_assoc in HP1.
  rewrite lpow_all0 in HP1.
  2: solve_const0_eq.
  apply HP1.
Qed.

End TM1.




