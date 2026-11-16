From BusyCoq Require Import Individual62 Longitudinal DivModCases ES_v3.
Require Import Lia List Arith String.

Open Scope list.

Section Rules.

Variable tm : TM.
Variable h1 h2 : list (DH0 * DH0).
Variable D1 D2 D3 D4 : nat -> list Sym.

Hypothesis D1_Inc : forall n, segRLs tm h1 [] (D1 n) (D2 (2+n)).
Hypothesis D2_Inc : forall n, segRLs tm h1 h1 (D2 n) (D1 n).
Hypothesis D3_Inc : forall n, segRLs tm h1 h2 (D3 n) (D2 (2+n)).
Hypothesis D4_Inc : forall n, segRLs tm h1 h2 (D4 n) (D2 (2+n)).
Hypothesis rh_Inc : sideRLs tm h1 0inf (D2 2 *> 0inf).
Hypothesis D1_Ov : forall n, segRLs tm h2 [] (D1 n) (D3 n).
Hypothesis D2_Ov : forall n, segRLs tm h2 [] (D2 n) (D4 n).
Hypothesis rh_Ov : sideRLs tm h2 0inf 0inf.

Inductive Num : nat -> side -> Prop :=
| Num_0 : Num 0 0inf
| Num_D1 n p r : Num n r -> 0 < n -> Num (n*2) (D1 (p*2) *> r)
| Num_D2 n p r : Num n r -> Num (1+n*2) (D2 (p*2) *> r).

Inductive Marked : nat -> side -> Prop :=
| Marked_D3 n p r : Num n r -> 0 < n -> Marked (n*2) (D3 (p*2) *> r)
| Marked_D4 n p r : Num n r -> Marked (1+n*2) (D4 (p*2) *> r).

Lemma h1_D2_even k p :
  segRLs tm (h1^^(k*2)) (h1^^k) (D2 p) (D2 (p+k*2)).
Proof.
  gen p; induction k; intros.
  - cbn. replace (p+0) with p by lia. constructor.
  - replace (S k*2) with (2+k*2) by lia.
    rewrite !lpow_add.
    eapply segRLs_trans.
    + assert (Hp: segRLs tm (h1^^2) (h1^^1) (D2 p) (D2 (2+p))).
      { eapply segRLs_trans_add with (n1:=1%nat) (n2:=1%nat)
          (n1':=1%nat) (n2':=0%nat) (w3:=D1 p);
          cbn[lpow]; rewrite !app_nil_r; [apply D2_Inc|apply D1_Inc]. }
      cbn[lpow] in Hp |- *. rewrite !app_nil_r in Hp |- *. apply Hp.
    + replace (p+(2+k*2)) with ((2+p)+k*2) by lia. apply IHk.
Qed.

Lemma h1_D2_odd k p :
  segRLs tm (h1^^(1+k*2)) (h1^^(k+1)) (D2 p) (D1 (p+k*2)).
Proof.
  replace (1+k*2) with (k*2+1) by lia.
  rewrite !lpow_add.
  cbn[lpow]. rewrite !app_nil_r.
  eapply @segRLs_trans with (w2:=D2 (p+k*2)) (ls2:=h1^^k) (ls3:=h1).
  - apply h1_D2_even.
  - apply D2_Inc.
Qed.

Lemma h1_D3_odd k p :
  segRLs tm (h1^^(1+k*2)) (h2++h1^^k)
    (D3 p) (D2 (p+(k+1)*2)).
Proof.
  rewrite lpow_add.
  eapply @segRLs_trans with (w2:=D2 (2+p)) (ls2:=h2) (ls3:=h1^^(k*2)).
  - cbn[lpow]. rewrite app_nil_r. apply D3_Inc.
  - replace (p+(k+1)*2) with ((2+p)+k*2) by lia.
    apply h1_D2_even.
Qed.

Lemma h1_D3_even k p :
  segRLs tm (h1^^((k+1)*2)) (h2++h1^^(k+1))
    (D3 p) (D1 (p+(k+1)*2)).
Proof.
  replace ((k+1)*2) with (1+(1+k*2)) by lia.
  rewrite lpow_add.
  eapply @segRLs_trans with (w2:=D2 (2+p)) (ls2:=h2) (ls3:=h1^^(1+k*2)).
  - cbn[lpow]. rewrite app_nil_r. apply D3_Inc.
  - replace (p+(1+(1+k*2))) with ((2+p)+k*2) by lia.
    apply h1_D2_odd.
Qed.

Lemma h1_D4_odd k p :
  segRLs tm (h1^^(1+k*2)) (h2++h1^^k)
    (D4 p) (D2 (p+(k+1)*2)).
Proof.
  rewrite lpow_add.
  eapply @segRLs_trans with (w2:=D2 (2+p)) (ls2:=h2) (ls3:=h1^^(k*2)).
  - cbn[lpow]. rewrite app_nil_r. apply D4_Inc.
  - replace (p+(k+1)*2) with ((2+p)+k*2) by lia.
    apply h1_D2_even.
Qed.

Lemma h1_D4_even k p :
  segRLs tm (h1^^((k+1)*2)) (h2++h1^^(k+1))
    (D4 p) (D1 (p+(k+1)*2)).
Proof.
  replace ((k+1)*2) with (1+(1+k*2)) by lia.
  rewrite lpow_add.
  eapply @segRLs_trans with (w2:=D2 (2+p)) (ls2:=h2) (ls3:=h1^^(1+k*2)).
  - cbn[lpow]. rewrite app_nil_r. apply D4_Inc.
  - replace (p+(1+(1+k*2))) with ((2+p)+k*2) by lia.
    apply h1_D2_odd.
Qed.

Lemma Num_zero r : Num 0 r -> r = 0inf.
Proof. intros H; inverts H; try lia; reflexivity. Qed.

Lemma Num_inc n r :
  Num n r ->
  exists r', sideRLs tm h1 r r' /\ Num (1+n) r'.
Proof.
  intros H; induction H as [|n p r Hnum IH Hnz|n p r Hnum IH].
  - exists (D2 2 *> 0inf); split; [apply rh_Inc|].
    replace (1+0) with (1+0*2) by reflexivity.
    eapply Num_D2 with (n:=0%nat) (p:=1%nat); constructor.
  - exists (D2 ((p+1)*2) *> r); split.
    + eapply segRLs_sideRLs_concat.
      * replace ((p+1)*2) with (2+p*2) by lia. apply D1_Inc.
      * constructor.
    + apply Num_D2, Hnum.
  - destruct IH as [r' [IH1 IH2]]. exists (D1 (p*2) *> r'); split.
    + eapply segRLs_sideRLs_concat; [apply D2_Inc|apply IH1].
    + replace (1+(1+n*2)) with ((1+n)*2) by lia.
      apply Num_D1; [apply IH2|lia].
Qed.

Lemma Num_incs k n r :
  Num n r ->
  exists r', sideRLs tm (h1^^k) r r' /\ Num (n+k) r'.
Proof.
  gen n r; induction k; intros.
  - exists r; split; [constructor|]. replace (n+0) with n by lia. assumption.
  - destruct (Num_inc n r H) as [r1 [I1 I2]].
    destruct (IHk _ _ I2) as [r2 [I3 I4]].
    exists r2; split.
    + cbn[lpow]. eapply sideRLs_trans; eassumption.
    + replace (n+S k) with ((1+n)+k) by lia. assumption.
Qed.

Lemma Num_mark n r :
  Num n r -> 0 < n ->
  exists r', sideRLs tm h2 r r' /\ Marked n r'.
Proof.
  intros H Hn; inverts H; try lia.
  - exists (D3 (p*2) *> r0); split.
    + eapply segRLs_sideRLs_concat; [apply D1_Ov|constructor].
    + apply Marked_D3; assumption.
  - exists (D4 (p*2) *> r0); split.
    + eapply segRLs_sideRLs_concat; [apply D2_Ov|constructor].
    + apply Marked_D4, H0.
Qed.

Lemma Marked_scan q r :
  Marked q r ->
  forall a, q <= a ->
  exists r', sideRLs tm (h1^^a) r r' /\ Num a r'.
Proof.
  gen r; induction q using lt_wf_ind; intros r0 HM a Hqa.
  inverts HM; destruct (mod2 a) as [k|k]; subst a.
  - destruct k; [lia|]. replace (S k) with (k+1) in * by lia.
    destruct (Num_mark n r H0 H1) as [rm [I1 I2]].
    destruct (H n ltac:(lia) rm I2 (k+1) ltac:(lia)) as [r' [I3 I4]].
    exists (D1 ((p+k+1)*2) *> r'); split.
    + eapply segRLs_sideRLs_concat.
      * replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia. apply h1_D3_even.
      * eapply sideRLs_trans; [apply I1|apply I3].
    + apply Num_D1; [apply I4|lia].
  - destruct (Num_mark n r H0 H1) as [rm [I1 I2]].
    destruct (H n ltac:(lia) rm I2 k ltac:(lia)) as [r' [I3 I4]].
    exists (D2 ((p+k+1)*2) *> r'); split.
    + eapply segRLs_sideRLs_concat.
      * replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia. apply h1_D3_odd.
      * eapply sideRLs_trans; [apply I1|apply I3].
    + apply Num_D2, I4.
  - destruct n.
    + apply Num_zero in H0; subst r.
      destruct k; [lia|]. replace (S k) with (k+1) in * by lia.
      destruct (Num_incs (k+1) 0 0inf Num_0) as [r' [I1 I2]].
      exists (D1 ((p+k+1)*2) *> r'); split.
      * eapply segRLs_sideRLs_concat.
        -- replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia. apply h1_D4_even.
        -- eapply sideRLs_trans; [apply rh_Ov|apply I1].
      * apply Num_D1; [apply I2|lia].
    + destruct k; [lia|]. replace (S k) with (k+1) in * by lia.
      destruct (Num_mark (S n) r H0 ltac:(lia)) as [rm [I1 I2]].
      destruct (H (S n) ltac:(lia) rm I2 (k+1) ltac:(lia)) as [r' [I3 I4]].
      exists (D1 ((p+k+1)*2) *> r'); split.
      * eapply segRLs_sideRLs_concat.
        -- replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia.
           apply h1_D4_even.
        -- eapply sideRLs_trans; [apply I1|apply I3].
      * apply Num_D1; [apply I4|lia].
  - destruct n.
    + apply Num_zero in H0; subst r.
      destruct (Num_incs k 0 0inf Num_0) as [r' [I1 I2]].
      exists (D2 ((p+k+1)*2) *> r'); split.
      * eapply segRLs_sideRLs_concat.
        -- replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia. apply h1_D4_odd.
        -- eapply sideRLs_trans; [apply rh_Ov|apply I1].
      * apply Num_D2, I2.
    + destruct (Num_mark (S n) r H0 ltac:(lia)) as [rm [I1 I2]].
      destruct (H (S n) ltac:(lia) rm I2 k ltac:(lia)) as [r' [I3 I4]].
      exists (D2 ((p+k+1)*2) *> r'); split.
      * eapply segRLs_sideRLs_concat.
        -- replace ((p+k+1)*2) with (p*2+(k+1)*2) by lia. apply h1_D4_odd.
        -- eapply sideRLs_trans; [apply I1|apply I3].
      * apply Num_D2, I4.
Qed.

Lemma prep2_D1 p :
  segRLs tm (h2++h1^^2) (h2++h1) (D1 (p*2)) (D1 ((p+1)*2)).
Proof.
  assert (H: segRLs tm (h2++h1^^2) (h2++h1^^1)
    (D1 (p*2)) (D1 ((p+1)*2))).
  { eapply @segRLs_trans with (w2:=D3 (p*2)) (ls2:=[]) (ls3:=h1^^2).
    - apply D1_Ov.
    - replace ((p+1)*2) with (p*2+(0+1)*2) by lia.
      apply (h1_D3_even 0%nat (p*2)). }
  cbn[lpow] in H |- *. applys_eq H;
    repeat rewrite app_nil_r; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma prep2_D2 p :
  segRLs tm (h2++h1^^2) (h2++h1) (D2 (p*2)) (D1 ((p+1)*2)).
Proof.
  assert (H: segRLs tm (h2++h1^^2) (h2++h1^^1)
    (D2 (p*2)) (D1 ((p+1)*2))).
  { eapply @segRLs_trans with (w2:=D4 (p*2)) (ls2:=[]) (ls3:=h1^^2).
    - apply D2_Ov.
    - replace ((p+1)*2) with (p*2+(0+1)*2) by lia.
      apply (h1_D4_even 0%nat (p*2)). }
  cbn[lpow] in H |- *. applys_eq H;
    repeat rewrite app_nil_r; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma prep1_D1 p :
  segRLs tm (h2++h1) h2 (D1 (p*2)) (D2 ((p+1)*2)).
Proof.
  assert (H: segRLs tm (h2++h1^^1) (h2++h1^^0)
    (D1 (p*2)) (D2 ((p+1)*2))).
  { eapply @segRLs_trans with (w2:=D3 (p*2)) (ls2:=[]) (ls3:=h1^^1).
    - apply D1_Ov.
    - replace ((p+1)*2) with (p*2+(0+1)*2) by lia.
      apply (h1_D3_odd 0%nat (p*2)). }
  cbn[lpow] in H |- *. applys_eq H;
    repeat rewrite app_nil_r; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma prep1_D2 p :
  segRLs tm (h2++h1) h2 (D2 (p*2)) (D2 ((p+1)*2)).
Proof.
  assert (H: segRLs tm (h2++h1^^1) (h2++h1^^0)
    (D2 (p*2)) (D2 ((p+1)*2))).
  { eapply @segRLs_trans with (w2:=D4 (p*2)) (ls2:=[]) (ls3:=h1^^1).
    - apply D2_Ov.
    - replace ((p+1)*2) with (p*2+(0+1)*2) by lia.
      apply (h1_D4_odd 0%nat (p*2)). }
  cbn[lpow] in H |- *. applys_eq H;
    repeat rewrite app_nil_r; repeat rewrite <-app_assoc; reflexivity.
Qed.

Lemma Num_view n r :
  Num n r -> 0 < n ->
  exists p q s, Num q s /\
    (n = q*2 /\ 0 < q /\ r = D1 (p*2) *> s \/
     n = 1+q*2 /\ r = D2 (p*2) *> s).
Proof.
  intros H Hn; inverts H; try lia.
  - exists p,n0,r0; tauto.
  - exists p,n0,r0; tauto.
Qed.

Lemma prepare p n rx :
  Num (1+n) rx -> 4 <= n ->
  exists u v q rm,
    sideRLs tm (h1^^5) (D4 (p*2) *> rx)
      (D2 ((p+3)*2) *> D1 ((u+1)*2) *> D2 ((v+1)*2) *> rm) /\
    Marked q rm /\ q*4 <= 1+n.
Proof.
  intros Hnum Hn.
  destruct (Num_view _ _ Hnum ltac:(lia)) as [u [q1 [r1 [Hq1 Hv1]]]].
  destruct Hv1 as [[E1 [Hq1p Er1]]|[E1 Er1]].
  all: destruct (Num_view _ _ Hq1 ltac:(lia)) as [v [q [r [Hq Hv2]]]].
  all: destruct Hv2 as [[E2 [Hqp Er]]|[E2 Er]].
  all: destruct (Num_mark q r Hq ltac:(lia)) as [rm [I1 I2]].
  all: exists u,v,q,rm; split; [|split; [apply I2|lia]].
  all: subst rx r1.
  all: eapply segRLs_sideRLs_concat.
  all: try (replace ((p+3)*2) with (p*2+(2+1)*2) by lia;
    apply (h1_D4_odd 2%nat (p*2))).
  all: eapply segRLs_sideRLs_concat.
  all: try first [apply prep2_D1|apply prep2_D2].
  all: eapply segRLs_sideRLs_concat.
  all: try first [apply prep1_D1|apply prep1_D2].
  all: apply I1.
Qed.

Lemma post_scan p u v q rm :
  Marked q rm -> q*4 <= p+8 ->
  exists r',
    sideRLs tm (h1^^(p*2+11))
      (D2 ((u+2)*2) *> D2 ((v+1)*2) *> rm)
      (D1 ((u+p+7)*2) *> r') /\
    Num (p+7) r'.
Proof.
  intros HM Hq; destruct (mod2 (p+6)) as [k|k]; subst.
  - destruct (Marked_scan _ _ HM k ltac:(lia)) as [r' [I1 I2]].
    exists (D2 ((v+k+1)*2) *> r'); split.
    + eapply segRLs_sideRLs_concat.
      * replace (p*2+11) with (1+(p+5)*2) by lia.
        replace ((u+p+7)*2) with ((u+2)*2+(p+5)*2) by lia.
        apply h1_D2_odd.
      * replace (p+5+1) with (k*2) by lia.
        eapply segRLs_sideRLs_concat.
        -- replace ((v+k+1)*2) with ((v+1)*2+k*2) by lia.
           apply h1_D2_even.
        -- apply I1.
    + replace (p+7) with (1+k*2) by lia.
      apply Num_D2, I2.
  - destruct (Marked_scan _ _ HM (k+1) ltac:(lia)) as [r' [I1 I2]].
    exists (D1 ((v+k+1)*2) *> r'); split.
    + eapply segRLs_sideRLs_concat.
      * replace (p*2+11) with (1+(p+5)*2) by lia.
        replace ((u+p+7)*2) with ((u+2)*2+(p+5)*2) by lia.
        apply h1_D2_odd.
      * replace (p+5+1) with (1+k*2) by lia.
        eapply segRLs_sideRLs_concat.
        -- replace ((v+k+1)*2) with ((v+1)*2+k*2) by lia.
           apply h1_D2_odd.
        -- apply I1.
    + replace (p+7) with ((k+1)*2) by lia.
      apply Num_D1; [apply I2|lia].
Qed.

Variable State : nat -> side -> Q * tape.

Hypothesis Inc : forall n r r', sideRLs tm h1 r r' ->
  progress tm (State (1+n) r) (State n r').
Hypothesis Ov1 : forall n r r', sideRLs tm h1 r r' ->
  progress tm (State 0 (D1 n *> r)) (State 5 (D4 n *> r')).
Hypothesis Ov2 : forall n r r', sideRLs tm h1 r r' ->
  progress tm (State 0 (D2 n *> r)) (State (5+n) r').

Lemma State_Incs k a r r' : sideRLs tm (h1^^k) r r' ->
  evstep tm (State (k+a) r) (State a r').
Proof.
  gen a r r'; induction k; intros.
  - cbn [lpow] in H. inverts H. constructor.
  - cbn [lpow] in H. apply sideRLs_split in H as [r0 [H0 H]].
    eapply evstep_trans.
    + replace (S k+a) with (1+(k+a)) by lia.
      apply progress_evstep,Inc,H0.
    + apply IHk,H.
Qed.

Inductive GoodR : side -> Prop :=
| GoodR_intro p n r : Num n r -> 4 <= n ->
    n*2 <= p*2+14 -> GoodR (D1 (p*2) *> r).

Lemma Good_step r : GoodR r ->
  exists r', progress tm (State 0 r) (State 0 r') /\ GoodR r'.
Proof.
  intros HG; inverts HG.
  destruct (Num_inc _ _ H) as [rx [Iinc Ninc]].
  destruct (prepare p n rx Ninc H0) as
    [u [v [q [rm [Iprep [Mrm Hq]]]]]].
  assert (Hq': q*4 <= p+8) by lia.
  destruct (post_scan p u v q rm Mrm Hq') as [r' [Ipost Npost]].
  assert (Iov2 :
    sideRLs tm h1
      (D1 ((u+1)*2) *> D2 ((v+1)*2) *> rm)
      (D2 ((u+2)*2) *> D2 ((v+1)*2) *> rm)).
  { eapply segRLs_sideRLs_concat.
    - replace ((u+2)*2) with (2+(u+1)*2) by lia. apply D1_Inc.
    - constructor. }
  exists (D1 ((u+p+7)*2) *> r'); split.
  - eapply progress_evstep_trans.
    + apply Ov1,Iinc.
    + eapply evstep_trans.
      * apply (State_Incs 5 0),Iprep.
      * eapply evstep_trans.
        -- apply progress_evstep.
           replace (p*2+11) with (5+(p+3)*2) by lia.
           apply Ov2,Iov2.
        -- replace (5+(p+3)*2) with (p*2+11) by lia.
           replace (p*2+11) with (p*2+11+0) by lia.
           apply (State_Incs (p*2+11) 0),Ipost.
  - apply GoodR_intro with (p:=u+p+7) (n:=p+7); [exact Npost|lia|lia].
Qed.

Lemma Good_nonhalt r : GoodR r -> ~ halts tm (State 0 r).
Proof.
  intros HG.
  eapply (progress_nonhalt_cond tm side r (fun r => State 0 r) GoodR).
  - intros r0 Hr0. apply Good_step,Hr0.
  - exact HG.
Qed.

Lemma initial_Num : Num 3 (D2 4 *> D2 2 *> 0inf).
Proof.
  change (Num (1+1*2) (D2 (2*2) *> D2 (1*2) *> 0inf)).
  exact (Num_D2 1 2 _ (Num_D2 0 1 _ Num_0)).
Qed.

Lemma initial_Good :
  exists r, sideRLs tm (h1^^11) (D2 4 *> D2 2 *> 0inf) r /\ GoodR r.
Proof.
  destruct (Num_incs 11 3 _ initial_Num) as [r [I N]].
  exists r; split; [exact I|].
  replace (3+11) with 14 in N by lia.
  destruct (Num_view 14 r N ltac:(lia)) as
    [p [n [r0 [N0 [[Hn [_ Er]]|[Hn Er]]]]]]; [|lia].
  subst r. replace n with 7 in * by lia.
  apply GoodR_intro with (p:=p) (n:=7); auto; lia.
Qed.

Lemma machine_nonhalt c :
  evstep tm c (State 11 (D2 4 *> D2 2 *> 0inf)) -> ~ halts tm c.
Proof.
  intros Iinit. destruct initial_Good as [r [I HG]].
  eapply multistep_nonhalt.
  - eapply evstep_trans; [exact Iinit|].
    apply (State_Incs 11 0),I.
  - apply Good_nonhalt,HG.
Qed.

End Rules.

Ltac es_v3_pre ::= ut.

Definition h1 : list (DH0*DH0) := [((D,<[1;0;1;0]),(A,[]))].
Definition h2 : list (DH0*DH0) := [((C,<[]),(B,[1;1]))].

Definition D1 n := [0;0;0;0;0;0] ++ [1;1]^^n.
Definition D2 n := [0;0;0;1;1;1] ++ [1;1]^^n.
Definition D3 n := [0;0;0;0] ++ [1;1]^^n.
Definition D4 n := [0;1;1;1] ++ [1;1]^^n.

Definition State '(n,r) :=
  0inf <* <[1;0]^^n {{{ (D,<[1;0;1;0],R) }}} r.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LA_0RE0RD_0RB1RC_1LD0LA_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma Inc n r r' : sideRLs tm h1 r r' ->
  State (1+n,r) -->+ State (n,r').
Proof.
  unfold State; intros H. eapply sideRLs_1 in H. follow10 H. es' n & r'.
Qed.

Lemma Ov1 n r r' : sideRLs tm h1 r r' ->
  State (O,D1 n *> r) -->+ State (5,D4 n *> r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Lemma Ov2 n r r' : sideRLs tm h1 r r' ->
  State (O,D2 n *> r) -->+ State (5+n,r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply (machine_nonhalt tm h1 h2 D1 D2 D3 D4 _ _ _ _ _ _ _ _
    (fun n r => State (n,r)) Inc Ov1 Ov2).
  Unshelve.
  all: esx.
Qed.

Print Assumptions nonhalt.

End TM1.

Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LA_0RE0RD_0RB0LD_1LA0LA_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma Inc n r r' : sideRLs tm h1 r r' ->
  State (1+n,r) -->+ State (n,r').
Proof.
  unfold State; intros H. eapply sideRLs_1 in H. follow10 H. es' n & r'.
Qed.

Lemma Ov1 n r r' : sideRLs tm h1 r r' ->
  State (O,D1 n *> r) -->+ State (5,D4 n *> r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Lemma Ov2 n r r' : sideRLs tm h1 r r' ->
  State (O,D2 n *> r) -->+ State (5+n,r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply (machine_nonhalt tm h1 h2 D1 D2 D3 D4 _ _ _ _ _ _ _ _
    (fun n r => State (n,r)) Inc Ov1 Ov2).
  Unshelve.
  all: esx.
Qed.

Print Assumptions nonhalt.

End TM2.

Module TM3.

Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC1LA_0RE0RD_0RB0LD_1LD0LA_0LE---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma Inc n r r' : sideRLs tm h1 r r' ->
  State (1+n,r) -->+ State (n,r').
Proof.
  unfold State; intros H. eapply sideRLs_1 in H. follow10 H. es' n & r'.
Qed.

Lemma Ov1 n r r' : sideRLs tm h1 r r' ->
  State (O,D1 n *> r) -->+ State (5,D4 n *> r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Lemma Ov2 n r r' : sideRLs tm h1 r r' ->
  State (O,D2 n *> r) -->+ State (5+n,r').
Proof.
  unfold State; intros H. es; er. eapply sideRLs_1 in H.
  follow100 H. es' n & r'.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  eapply (machine_nonhalt tm h1 h2 D1 D2 D3 D4 _ _ _ _ _ _ _ _
    (fun n r => State (n,r)) Inc Ov1 Ov2).
  Unshelve.
  all: esx.
Qed.

Print Assumptions nonhalt.

End TM3.

