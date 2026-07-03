From BusyCoq Require Import Individual62 LongN.
Require Import Lia.
Require Import List.
Require Import PeanoNat.
Require Import Bool.

Module InfiniteRectInternal.

Fixpoint sym_list_eqb (a b : list Sym) :=
match a,b with
| [], [] => true
| x::xs, y::ys => if sym_eqb x y then sym_list_eqb xs ys else false
| _, _ => false
end.

Lemma sym_list_eqb_spec a b:
  Bool.reflect (a=b) (sym_list_eqb a b).
Proof.
  gen b.
  induction a as [|x xs IH]; destruct b as [|y ys]; cbn.
  - constructor.
    reflexivity.
  - constructor.
    congruence.
  - constructor.
    congruence.
  - destruct (sym_eqb_spec x y) as [Heq|Hneq].
    + subst.
      destruct (IH ys) as [Heq|Hneq].
      * subst.
        constructor.
        reflexivity.
      * constructor.
        intro H.
        inversion H; subst.
        contradiction.
    + constructor.
      intro H.
      inversion H; subst.
      contradiction.
Qed.

Definition sideS_n tm (H : Stream (DH0*DH0)) (r : side) (n : nat) : Prop :=
  exists k, sideRLs_n tm (Str_firstn k H) r n.

Definition downRect tm (L R : Stream (DH0*DH0)) (w : list Sym) (width : nat) : Prop :=
  forall r n,
    sideS_n tm R r n ->
    sideS_n tm L (w *> r) (width + n).

Definition quadRect tm (L : Stream (DH0*DH0)) (top : side) : Prop :=
  forall n, sideS_n tm L top n.

Definition leftRealizes tm (h : DH0) (L : Stream (DH0*DH0)) (l : side) : Prop :=
  forall k, exists ls h' l',
    lcons h ls = (Str_firstn k L, h') /\
    sideRLs (flip tm) ls l l'.

Lemma Str_firstn_length {A} n (s : Stream A):
  length (Str_firstn n s) = n.
Proof.
  gen s.
  induction n; intros; cbn.
  - reflexivity.
  - rewrite IHn.
    reflexivity.
Qed.

Lemma Str_firstn_add {A} n m (s : Stream A):
  Str_firstn (n+m) s =
  Str_firstn n s ++ Str_firstn m (Str_nth_tl n s).
Proof.
  gen s.
  induction n; intros; cbn; trivial.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Str_firstn_app {A} (xs : list A) (s : Stream A):
  Str_firstn (length xs) (xs *> s) = xs.
Proof.
  induction xs; cbn.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma Str_firstn_app_add {A} (xs : list A) n (s : Stream A):
  Str_firstn (length xs+n) (xs *> s) = xs ++ Str_firstn n s.
Proof.
  induction xs; cbn.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma Str_firstn_app_le {A} n (xs : list A) (s : Stream A):
  n <= length xs ->
  Str_firstn n (xs *> s) = firstn n xs.
Proof.
  gen xs.
  induction n; intros xs Hle; cbn.
  - reflexivity.
  - destruct xs; cbn in *.
    + lia.
    + rewrite IHn by lia.
      reflexivity.
Qed.

Lemma lcons_app h ls1 hs1 h1 ls2 hs2 h2:
  lcons h ls1 = (hs1,h1) ->
  lcons h1 ls2 = (hs2,h2) ->
  lcons h (ls1++ls2) = (hs1++hs2,h2).
Proof.
  gen h hs1 h1.
  induction ls1 as [|[a b] ls1 IH]; intros h hs1 h1 H1 H2; cbn in *.
  - inversion H1; subst.
    exact H2.
  - destruct (lcons b ls1) as [hs0 h0] eqn:E.
    inversion H1; subst.
    rewrite (IH b hs0 h1 E H2).
    reflexivity.
Qed.

Lemma lcons_firstn h ls hs h' k:
  lcons h ls = (hs,h') ->
  k <= length hs ->
  exists h0, lcons h (firstn k ls) = (firstn k hs,h0).
Proof.
  gen h ls hs h'.
  induction k; intros h ls hs h' H Hle.
  - exists h.
    reflexivity.
  - destruct ls as [|[a b] ls].
    + cbn in H.
      inversion H; subst.
      cbn in Hle.
      lia.
    + cbn in H.
      destruct (lcons b ls) as [hs0 h0] eqn:E.
      inversion H; subst.
      cbn in Hle.
      destruct (IHk b ls hs0 h' E) as [h1 H1]; [lia|].
      exists h1.
      cbn.
      rewrite H1.
      reflexivity.
Qed.

Lemma lcons_sideRLs_prefix tm h ls hs h' l l' k:
  lcons h ls = (hs,h') ->
  sideRLs tm ls l l' ->
  k <= length hs ->
  exists ls0 h0 l0,
    lcons h ls0 = (firstn k hs,h0) /\
    sideRLs tm ls0 l l0.
Proof.
  intros Hlcons Hside Hle.
  destruct (lcons_firstn h ls hs h' k Hlcons Hle) as [h0 Hprefix].
  pose proof (firstn_skipn k ls) as Hsplit.
  rewrite <- Hsplit in Hside.
  apply sideRLs_split in Hside.
  destruct Hside as [l0 [Hside _]].
  exists (firstn k ls), h0, l0.
  split; assumption.
Qed.

Lemma sideRLs_n_prefix_extend tm H r n k1 k2:
  k1 <= k2 ->
  sideRLs_n tm (Str_firstn k1 H) r n ->
  sideRLs_n tm (Str_firstn k2 H) r n.
Proof.
  intros Hle Hs.
  replace k2 with (k1 + (k2-k1)) by lia.
  rewrite Str_firstn_add.
  eapply sideRLs_n_trans_1.
  exact Hs.
Qed.

Lemma sideS_n_0 tm H r:
  sideS_n tm H r O.
Proof.
  exists O.
  cbn.
  constructor.
Qed.

Lemma sideS_n_mono tm H r n m:
  sideS_n tm H r n ->
  m <= n ->
  sideS_n tm H r m.
Proof.
  intros [k Hs] Hle.
  exists k.
  eapply sideRLs_n_mono; eauto.
Qed.

Lemma sideS_n_after tm H r n:
  sideS_n tm H r n ->
  forall k0, exists k,
    k0 <= k /\
    sideRLs_n tm (Str_firstn k H) r n.
Proof.
  intros [k Hs] k0.
  exists (k + k0).
  split.
  - lia.
  - eapply (sideRLs_n_prefix_extend tm H r n k (k+k0)); eauto; lia.
Qed.

Lemma sideS_n_app_split tm hs H r n:
  sideS_n tm (hs *> H) r n ->
  sideRLs_n tm hs r n \/
  exists r', sideRLs tm hs r r' /\ sideS_n tm H r' n.
Proof.
  intros [k Hs].
  destruct (Nat.leb_spec k (length hs)) as [Hle|Hgt].
  - left.
    eapply (sideRLs_n_prefix_extend tm (hs *> H) r n k (length hs)) in Hs; eauto.
    rewrite Str_firstn_app in Hs.
    exact Hs.
  - replace k with (length hs+(k-length hs)) in Hs by lia.
    rewrite Str_firstn_app_add in Hs.
    apply sideRLs_n_split in Hs.
    destruct Hs as [Hs|[r' [Hside Hs]]].
    + left.
      exact Hs.
    + right.
      exists r'.
      split; [exact Hside|].
      exists (k-length hs).
      exact Hs.
Qed.

Lemma sideS_n_app_left tm hs H r n:
  sideRLs_n tm hs r n ->
  sideS_n tm (hs *> H) r n.
Proof.
  intros Hs.
  exists (length hs).
  rewrite Str_firstn_app.
  exact Hs.
Qed.

Lemma sideS_n_app_right tm hs H r r' n:
  sideRLs tm hs r r' ->
  sideS_n tm H r' n ->
  sideS_n tm (hs *> H) r n.
Proof.
  intros Hside [k Hs].
  exists (length hs+k).
  rewrite Str_firstn_app_add.
  eapply sideRLs_n_trans_2; eauto.
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

Inductive segRLs_n1_tail tm:
  list (DH0*DH0) -> list (DH0*DH0) -> list Sym -> list Sym -> Prop :=
| segRLs_n1_tail_O w:
    segRLs_n1_tail tm [] [] w w
| segRLs_n1_tail_S ls1 ls2 w1 w2:
    segRLs_n tm ls1 ls2 w1 w2 1 ->
    segRLs_n1_tail tm ls1 ls2 w1 w2.

Lemma segRLs_n_cons_segRL tm h1 h2 ls1 ls2 w1 w2 w3:
  segRL tm h1 h2 w1 w2 ->
  segRLs_n tm ls1 ls2 w2 w3 1 ->
  segRLs_n tm ((h1,h2)::ls1) ls2 w1 w3 1.
Proof.
  unfold segRLs_n.
  intros Hhead [Htail_n Htail].
  split; intros.
  - econstructor 1.
    + intro l.
      apply Hhead.
    + apply Htail_n.
      exact H.
    + lia.
  - econstructor.
    + intro l.
      apply Hhead.
    + apply Htail.
      exact H.
Qed.

Lemma segRLs_n_cons_tail tm h1 h2 ls1 ls2 w1 w2 w3:
  segRL tm h1 h2 w1 w2 ->
  segRLs_n1_tail tm ls1 ls2 w2 w3 ->
  segRLs_n tm ((h1,h2)::ls1) ls2 w1 w3 1.
Proof.
  intros Hhead Htail.
  inversion Htail; subst.
  - apply segRLs_n_S.
    exact Hhead.
  - eapply segRLs_n_cons_segRL; eauto.
Qed.

Lemma lrcons_rcons h1 ls h2 h2' ls':
  rcons ls h2 = (h2',ls') ->
  (h1,h2')::ls' = lrcons h1 ls h2.
Proof.
  destruct ls as [|[a b] ls]; cbn; intros H.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
Qed.

Definition segLLs_n1 tm h1 ls1 h2 ls2 w1 w2 :=
  exists lsLR lsMid lsTail wLR wAfter hFinal,
    ls2 = lsMid++lsTail /\
    rcons lsLR hFinal = (h2,lsMid) /\
    segLRs tm lsLR w1 wLR /\
    segLL tm hFinal h1 wLR wAfter /\
    segRLs_n1_tail tm ls1 lsTail wAfter w2.

Lemma segRLs_n_lrcons_tail tm ls2 ls3 ls4 w1 w2 w3 w4 w5 h1 h2 h3 h4:
  segRR' tm h1 h3 w1 w3 ->
  segLL tm h4 h2 w4 w5 ->
  segLRs tm ls2 w3 w4 ->
  segRLs_n1_tail tm ls3 ls4 w5 w2 ->
  segRLs_n tm ((h1,h2)::ls3) (lrcons h3 ls2 h4++ls4) w1 w2 1.
Proof.
  intros Hrr Hll Hlr Htail.
  inversion Htail; subst.
  - rewrite app_nil_r.
    eapply segRLs_n_lrcons; eauto.
  - change ((h1,h2)::ls3) with ([(h1,h2)]++ls3).
    eapply (segRLs_n_trans tm [(h1,h2)] (lrcons h3 ls2 h4)
      ls3 ls4 w1 w5 w2 1 1 1).
    + eapply segRLs_n_lrcons; eauto.
    + exact H.
    + lia.
    + lia.
Qed.

Lemma segRLs_n_RR_LLs tm ls3 ls4 w1 w2 w3 h1 h2 h3 h4:
  segRR' tm h1 h3 w1 w3 ->
  segLLs_n1 tm h2 ls3 h4 ls4 w3 w2 ->
  segRLs_n tm ((h1,h2)::ls3) ((h3,h4)::ls4) w1 w2 1.
Proof.
  intros Hrr
    (lsLR & lsMid & lsTail & wLR & wAfter & hFinal &
      Hls4 & Hrcons & Hlr & Hll & Htail).
  subst ls4.
  change ((h3,h4)::lsMid++lsTail) with (((h3,h4)::lsMid)++lsTail).
  rewrite (lrcons_rcons h3 lsLR hFinal h4 lsMid Hrcons).
  eapply segRLs_n_lrcons_tail; eauto.
Qed.

Fixpoint segRLs_n1_c tm (ls1 ls2:list (DH0*DH0)) (w1 w2:list Sym) (T:nat) {struct T} :=
match T with
| O => false
| S T =>
match ls1 with
| ((QR,qR),(QL,qL))::ls1 =>
  match BoundedConfig.steps1 tm T (BoundedConfig.Build_T qR w1 QR R) with
  | Some (BoundedConfig.Build_T l r q L, true) =>
    match ls1, ls2 with
    | [], [] =>
      andb (sym_list_eqb r []) (andb (q_eqb q QL)
      match skip_prefix_list qL l with
      | Some w => sym_list_eqb w w2
      | None => false
      end)
    | _::_, _ =>
      andb (sym_list_eqb r []) (andb (q_eqb q QL)
      match skip_prefix_list qL l with
      | Some w => segRLs_n1_c tm ls1 ls2 w w2 T
      | None => false
      end)
    | _, _ => false
    end
  | Some (BoundedConfig.Build_T l r q R, true) =>
    match ls2 with
    | ((QR',qR'),hL')::ls2 =>
      andb (sym_list_eqb r []) (andb (q_eqb q QR')
      match skip_prefix_list qR' l with
      | Some w => segLLs_n1_c tm (QL,qL) ls1 hL' ls2 w w2 T
      | None => false
      end)
    | [] => false
    end
  | _ => false
  end
| [] => false
end
end
with segLLs_n1_c tm h1 ls1 h2 ls2 w1 w2 T {struct T} :=
match T with
| O => false
| S T =>
let '(QL,qL) := h2 in
match BoundedConfig.steps1 tm T (BoundedConfig.Build_T qL w1 QL L) with
| Some (BoundedConfig.Build_T l r q R, flag) =>
  match ls2 with
  | ((QR',qR'),hL')::ls2 =>
    andb (sym_list_eqb r []) (andb (q_eqb q QR')
    match skip_prefix_list qR' l with
    | Some w => segLLs_n1_c tm h1 ls1 hL' ls2 w w2 T
    | None => false
    end)
  | [] => false
  end
| Some (BoundedConfig.Build_T l r q L, flag) =>
  let '(QL0,qL0) := h1 in
  andb (sym_list_eqb r []) (andb (q_eqb q QL0)
  match skip_prefix_list qL0 l with
  | Some w =>
    match ls1, ls2 with
    | [], [] => sym_list_eqb w w2
    | [], _ => false
    | _::_, _ => segRLs_n1_c tm ls1 ls2 w w2 T
    end
  | None => false
  end)
| _ => false
end
end.

Ltac split_andb H :=
  repeat match type of H with
  | andb _ _ = true =>
    let Ha := fresh "H" in
    apply andb_true_iff in H as [Ha H]
  end.

Lemma segRLs_LLs_n1_c_spec tm T:
  (forall ls1 ls2 w1 w2,
    segRLs_n1_c tm ls1 ls2 w1 w2 T = true ->
    segRLs_n tm ls1 ls2 w1 w2 1) /\
  (forall h1 ls1 h2 ls2 w1 w2,
    segLLs_n1_c tm h1 ls1 h2 ls2 w1 w2 T = true ->
    segLLs_n1 tm h1 ls1 h2 ls2 w1 w2).
Proof.
  induction T as [|T IH]; cbn [segRLs_n1_c segLLs_n1_c]; split; intros; try congruence.
  - destruct IH as [IHseg IHll].
    destruct ls1 as [|[[QR qR] [QL qL]] ls1]; cbn in H; [congruence|].
    pose proof (BoundedConfig.steps1_spec tm T
      (BoundedConfig.Build_T qR w1 QR R)) as Hstep.
    destruct (BoundedConfig.steps1 tm T
      (BoundedConfig.Build_T qR w1 QR R)) as [[x flag]|] eqn:Estep;
      [|congruence].
    destruct x as [l r q d].
    destruct d; destruct flag; cbn in H; try congruence.
    + destruct ls1 as [|p ls1'].
      * destruct ls2 as [|p ls2']; cbn in H; [|congruence].
        split_andb H.
        destruct (sym_list_eqb_spec r []); [subst|congruence].
        destruct (q_eqb_spec q QL); [subst|congruence].
        destruct (skip_prefix_list qL l) as [w|] eqn:ESkip; cbn in H;
          [|congruence].
        apply skip_prefix_list_spec in ESkip.
        assert (Hfirst: segRL tm (QR,qR) (QL,qL) w1 w).
        {
          unfold segRL.
          intros l0 r0.
          specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          exact Hstep.
        }
        destruct (sym_list_eqb_spec w w2); [subst|congruence].
        eapply segRLs_n_cons_tail.
        -- exact Hfirst.
        -- constructor.
      * split_andb H.
        destruct (sym_list_eqb_spec r []); [subst|congruence].
        destruct (q_eqb_spec q QL); [subst|congruence].
        destruct (skip_prefix_list qL l) as [w|] eqn:ESkip; cbn in H;
          [|congruence].
        apply skip_prefix_list_spec in ESkip.
        assert (Hfirst: segRL tm (QR,qR) (QL,qL) w1 w).
        {
          unfold segRL.
          intros l0 r0.
          specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          exact Hstep.
        }
        eapply segRLs_n_cons_tail.
        -- exact Hfirst.
        -- constructor.
           eapply IHseg.
           exact H.
    + destruct ls2 as [|[[QR' qR'] hL'] ls2]; cbn in H; [congruence|].
      split_andb H.
      destruct (sym_list_eqb_spec r []); [subst|congruence].
      destruct (q_eqb_spec q QR'); [subst|congruence].
      destruct (skip_prefix_list qR' l) as [w|] eqn:ESkip; cbn in H;
        [|congruence].
      apply skip_prefix_list_spec in ESkip.
      eapply segRLs_n_RR_LLs.
      * unfold segRR'.
        intros l0 r0.
        specialize (Hstep l0 r0).
        cbn in Hstep.
        rewrite ESkip in Hstep.
        rewrite Str_app_assoc in Hstep.
        exact Hstep.
      * eapply IHll.
        exact H.
  - destruct IH as [IHseg IHll].
    destruct h2 as [QL qL].
    pose proof (BoundedConfig.steps1_spec tm T
      (BoundedConfig.Build_T qL w1 QL L)) as Hstep.
    destruct (BoundedConfig.steps1 tm T
      (BoundedConfig.Build_T qL w1 QL L)) as [[x flag]|] eqn:Estep;
      [|congruence].
    destruct x as [l r q d].
    destruct d; cbn in H.
    + destruct h1 as [QL0 qL0].
      split_andb H.
      destruct (sym_list_eqb_spec r []); [subst|congruence].
      destruct (q_eqb_spec q QL0); [subst|congruence].
      destruct (skip_prefix_list qL0 l) as [w|] eqn:ESkip; cbn in H;
        [|congruence].
      apply skip_prefix_list_spec in ESkip.
      assert (Hll: segLL tm (QL,qL) (QL0,qL0) w1 w).
      {
        unfold segLL.
        intros l0 r0.
        destruct flag.
        - apply progress_evstep.
          specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          exact Hstep.
        - specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          exact Hstep.
      }
      destruct ls1 as [|p ls1'].
      * destruct ls2 as [|p ls2']; cbn in H; [|congruence].
        destruct (sym_list_eqb_spec w w2); [subst|congruence].
        exists (@nil (DH0*DH0)), (@nil (DH0*DH0)), (@nil (DH0*DH0)),
          w1, w2, (QL,qL).
        repeat split.
        -- constructor.
        -- exact Hll.
        -- constructor.
      * exists (@nil (DH0*DH0)), (@nil (DH0*DH0)), ls2, w1, w, (QL,qL).
        repeat split.
        -- constructor.
        -- exact Hll.
        -- constructor.
           eapply IHseg.
           exact H.
    + destruct ls2 as [|[[QR' qR'] hL'] ls2]; cbn in H; [congruence|].
      split_andb H.
      destruct (sym_list_eqb_spec r []); [subst|congruence].
      destruct (q_eqb_spec q QR'); [subst|congruence].
      destruct (skip_prefix_list qR' l) as [w|] eqn:ESkip; cbn in H;
        [|congruence].
      apply skip_prefix_list_spec in ESkip.
      assert (Hlr: segLR tm (QL,qL) (QR',qR') w1 w).
      {
        unfold segLR.
        intros l0 r0.
        destruct flag.
        - specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          eapply progress_evstep.
          exact Hstep.
        - specialize (Hstep l0 r0).
          cbn in Hstep.
          rewrite ESkip in Hstep.
          rewrite Str_app_assoc in Hstep.
          exact Hstep.
      }
      destruct (IHll h1 ls1 hL' ls2 w w2 H)
        as (lsLR & lsMid & lsTail & wLR & wAfter & hFinal &
          Hls2 & Hrcons & HlrTail & Hll & Htail).
      subst ls2.
      exists (((QL,qL),(QR',qR'))::lsLR),
        (((QR',qR'),hL')::lsMid), lsTail, wLR, wAfter, hFinal.
      repeat split; eauto.
      * cbn.
        rewrite <- (lrcons_rcons (QR',qR') lsLR hFinal hL' lsMid Hrcons).
        reflexivity.
      * econstructor; eauto.
Qed.

Lemma segRLs_n1_c_spec tm ls1 ls2 w1 w2 T:
  segRLs_n1_c tm ls1 ls2 w1 w2 T = true ->
  segRLs_n tm ls1 ls2 w1 w2 1.
Proof.
  pose proof (segRLs_LLs_n1_c_spec tm T) as [Hspec _].
  apply Hspec.
Qed.

Lemma downRect_concat tm L M R w1 w2 width1 width2:
  downRect tm L M w1 width1 ->
  downRect tm M R w2 width2 ->
  downRect tm L R (w1++w2) (width1+width2).
Proof.
  unfold downRect.
  intros H1 H2 r n HR.
  specialize (H2 r n HR).
  specialize (H1 (w2 *> r) (width2+n) H2).
  replace ((width1 + width2) + n) with (width1 + (width2+n)) by lia.
  rewrite Str_app_assoc.
  exact H1.
Qed.

Lemma downRect_quadRect_concat tm L R w width top:
  downRect tm L R w width ->
  quadRect tm R top ->
  quadRect tm L (w *> top).
Proof.
  unfold quadRect.
  intros Hrect Hquad n.
  eapply sideS_n_mono with (n:=width+n).
  - apply Hrect.
    apply Hquad.
  - lia.
Qed.

Lemma segRLs_n_downRect_trans tm hL hR L R w1 w2 width:
  segRLs_n tm hL hR w1 w2 width ->
  downRect tm L R w2 width ->
  downRect tm (hL *> L) (hR *> R) w1 width.
Proof.
  unfold downRect.
  intros [Hseg_n Hseg] Hrect r n HR.
  destruct (sideS_n_app_split tm hR R r n HR) as [HR'|[r' [Hside HR']]].
  - apply sideS_n_app_left.
    apply Hseg_n.
    exact HR'.
  - eapply sideS_n_app_right.
    + apply Hseg.
      exact Hside.
    + apply Hrect.
      exact HR'.
Qed.

Lemma downRect_width_mono tm L R w width width':
  downRect tm L R w width ->
  width' <= width ->
  downRect tm L R w width'.
Proof.
  unfold downRect.
  intros H Hle r n HR.
  eapply sideS_n_mono.
  - apply H. exact HR.
  - lia.
Qed.

Lemma downRect_of_segRLs_n tm L R w width
  (I : Type) (KL KR : I -> nat) (bot : I -> list Sym):
  (forall kR0, exists i,
    kR0 <= KR i /\
    segRLs_n tm
      (Str_firstn (KL i) L)
      (Str_firstn (KR i) R)
      w (bot i) width) ->
  downRect tm L R w width.
Proof.
  unfold downRect, sideS_n.
  intros Hrect r n [kR HR].
  destruct (Hrect kR) as [i [Hle Hseg]].
  exists (KL i).
  destruct Hseg as [Hseg _].
  apply Hseg.
  eapply sideRLs_n_prefix_extend; eauto.
Qed.

Lemma downRect_segRLs_progress_iter tm width
  (P : Stream (DH0*DH0) -> Stream (DH0*DH0) -> list Sym -> Prop):
  (forall L R top, P L R top -> exists hL hR bot L' R',
    O < length hR /\
    L = hL *> L' /\
    R = hR *> R' /\
    segRLs_n tm hL hR top bot width /\
    P L' R' bot) ->
  forall n L R top,
    P L R top ->
    exists hL hR bot L' R',
      n <= length hR /\
      L = hL *> L' /\
      R = hR *> R' /\
      segRLs_n tm hL hR top bot width /\
      P L' R' bot.
Proof.
  intros Hprog.
  induction n; intros L R top HP.
  - destruct (Hprog L R top HP) as [hL [hR [bot [L' [R' [Hlen [HL [HR [Hseg HP']]]]]]]]].
    exists hL, hR, bot, L', R'.
    split; [lia|].
    split; [exact HL|].
    split; [exact HR|].
    split; [exact Hseg|exact HP'].
  - destruct (Hprog L R top HP) as [hL1 [hR1 [mid [L1 [R1 [Hlen1 [HL1 [HR1 [Hseg1 HP1]]]]]]]]].
    destruct (IHn L1 R1 mid HP1)
      as [hL2 [hR2 [bot [L2 [R2 [Hle [HL2 [HR2 [Hseg2 HP2]]]]]]]]].
    exists (hL1++hL2), (hR1++hR2), bot, L2, R2.
    split; [rewrite length_app; lia|].
    split.
    + rewrite HL1, HL2, Str_app_assoc.
      reflexivity.
    + split.
      * rewrite HR1, HR2, Str_app_assoc.
        reflexivity.
      * split.
        -- eapply segRLs_n_trans; eauto; lia.
        -- exact HP2.
Qed.

Lemma segRLs_n_inf_trans tm L R w width
  (P : Stream (DH0*DH0) -> Stream (DH0*DH0) -> list Sym -> Prop):
  (forall L0 R0 top, P L0 R0 top -> exists hL hR bot L' R',
    O < length hR /\
    L0 = hL *> L' /\
    R0 = hR *> R' /\
    segRLs_n tm hL hR top bot width /\
    P L' R' bot) ->
  P L R w ->
  downRect tm L R w width.
Proof.
  unfold downRect, sideS_n.
  intros Hprog HP0 r n [kR HR].
  destruct (downRect_segRLs_progress_iter tm width P Hprog kR L R w HP0)
    as [hL [hR [bot [L' [R' [Hle [HL [HR' [Hseg _]]]]]]]]].
  exists (length hL).
  rewrite HL.
  rewrite Str_firstn_app.
  destruct Hseg as [Hseg _].
  apply Hseg.
  assert (Hside: sideRLs_n tm (Str_firstn (length hR) R) r n).
  {
    eapply sideRLs_n_prefix_extend; eauto.
  }
  rewrite HR' in Hside.
  rewrite Str_firstn_app in Hside.
  exact Hside.
Qed.

Lemma leftRealizes_progress_iter tm
  (P : DH0 -> Stream (DH0*DH0) -> side -> Prop):
  (forall h L l, P h L l -> exists hs L' h' ls l',
    O < length hs /\
    L = hs *> L' /\
    lcons h ls = (hs,h') /\
    sideRLs (flip tm) ls l l' /\
    P h' L' l') ->
  forall n h L l,
    P h L l ->
    exists hs L' h' ls l',
      n <= length hs /\
      L = hs *> L' /\
      lcons h ls = (hs,h') /\
      sideRLs (flip tm) ls l l' /\
      P h' L' l'.
Proof.
  intros Hprog.
  induction n; intros h L l HP.
  - destruct (Hprog h L l HP) as [hs [L' [h' [ls [l' [Hlen [HL [Hlcons [Hside HP']]]]]]]]].
    exists hs, L', h', ls, l'.
    split; [lia|].
    split; [exact HL|].
    split; [exact Hlcons|].
    split; [exact Hside|exact HP'].
  - destruct (Hprog h L l HP) as [hs1 [L1 [h1 [ls1 [l1 [Hlen1 [HL1 [Hlcons1 [Hside1 HP1]]]]]]]]].
    destruct (IHn h1 L1 l1 HP1)
      as [hs2 [L2 [h2 [ls2 [l2 [Hle [HL2 [Hlcons2 [Hside2 HP2]]]]]]]]].
    exists (hs1++hs2), L2, h2, (ls1++ls2), l2.
    split; [rewrite length_app; lia|].
    split.
    + rewrite HL1, HL2, Str_app_assoc.
      reflexivity.
    + split.
      * eapply lcons_app; eauto.
      * split.
        -- eapply sideRLs_trans; eauto.
        -- exact HP2.
Qed.

Lemma leftRealizes_inf_concat tm h L l
  (P : DH0 -> Stream (DH0*DH0) -> side -> Prop):
  (forall h0 L0 l0, P h0 L0 l0 -> exists hs L' h' ls l',
    O < length hs /\
    L0 = hs *> L' /\
    lcons h0 ls = (hs,h') /\
    sideRLs (flip tm) ls l0 l' /\
    P h' L' l') ->
  P h L l ->
  leftRealizes tm h L l.
Proof.
  unfold leftRealizes.
  intros Hprog HP k.
  destruct (leftRealizes_progress_iter tm P Hprog k h L l HP)
    as [hs [L' [h' [ls [l' [Hle [HL [Hlcons [Hside _]]]]]]]]].
  destruct (lcons_sideRLs_prefix (flip tm) h ls hs h' l l' k Hlcons Hside Hle)
    as [ls0 [h0 [l0 [Hlcons0 Hside0]]]].
  exists ls0, h0, l0.
  split.
  - rewrite HL.
    rewrite Str_firstn_app_le by exact Hle.
    exact Hlcons0.
  - exact Hside0.
Qed.

Lemma sideRLs_leftRealizes_trans tm h hs L l h' ls l':
  lcons h ls = (hs,h') ->
  sideRLs (flip tm) ls l l' ->
  leftRealizes tm h' L l' ->
  leftRealizes tm h (hs *> L) l.
Proof.
  unfold leftRealizes.
  intros Hlcons Hside Htail k.
  destruct (Nat.leb_spec k (length hs)) as [Hle|Hgt].
  - destruct (lcons_sideRLs_prefix (flip tm) h ls hs h' l l' k
      Hlcons Hside Hle) as [ls0 [h0 [l0 [Hlcons0 Hside0]]]].
    exists ls0, h0, l0.
    split.
    + rewrite Str_firstn_app_le by exact Hle.
      exact Hlcons0.
    + exact Hside0.
  - destruct (Htail (k-length hs)) as [ls0 [h0 [l0 [Hlcons0 Hside0]]]].
    exists (ls++ls0), h0, l0.
    split.
    + rewrite (lcons_app h ls hs h' ls0 (Str_firstn (k-length hs) L) h0
        Hlcons Hlcons0).
      replace k with (length hs+(k-length hs)) by lia.
      rewrite Str_firstn_app_add.
      replace (length hs + (k - length hs) - length hs)
        with (k-length hs) by lia.
      reflexivity.
    + eapply sideRLs_trans; eauto.
Qed.

Lemma downRect_inf_concat tm L top
  (P : Stream (DH0*DH0) -> side -> Prop):
  (forall L0 top0, P L0 top0 -> exists L' top' w width,
    O < width /\
    top0 = w *> top' /\
    downRect tm L0 L' w width /\
    P L' top') ->
  P L top ->
  quadRect tm L top.
Proof.
  intros Hstep.
  assert (H: forall n L0 top0, P L0 top0 -> sideS_n tm L0 top0 n).
  {
    induction n; intros L0 top0 HP.
    - apply sideS_n_0.
    - destruct (Hstep L0 top0 HP) as [L' [top' [w [width [Hwidth [HT [Hrect HP']]]]]]].
      rewrite HT.
      eapply sideS_n_mono.
      + apply Hrect.
        apply IHn.
        exact HP'.
      + lia.
  }
  intros HP n.
  apply H.
  exact HP.
Qed.

Lemma quadRect_runs tm L top h l:
  quadRect tm L top ->
  leftRealizes tm h L l ->
  forall n, exists c,
    l {{{ (h,R) }}} top -[ tm ]->> n / c.
Proof.
  intros Hrect Hleft n.
  destruct (sideS_n_after tm L top n (Hrect n) n) as [k [Hnk Hside]].
  destruct (Hleft k) as [ls [h' [l' [Hlcons Hflip]]]].
  eapply sideRLs_n_sideRLs_concat in Hside.
  4: exact Hflip.
  2: exact Hlcons.
  2: rewrite Str_firstn_length; exact Hnk.
  exact Hside.
Qed.

Lemma quadRect_nonhalt tm L top h l:
  quadRect tm L top ->
  leftRealizes tm h L l ->
  ~halts tm (l {{{ (h,R) }}} top).
Proof.
  intros Hrect Hleft.
  apply step_unbounded_nonhalt.
  apply (quadRect_runs tm L top h l); assumption.
Qed.

Lemma progress_rect_nonhalt_cond tm L top
  (P : Stream (DH0*DH0) -> side -> Prop) h l:
  (forall L0 top0, P L0 top0 -> exists L' top' w width,
    O < width /\
    top0 = w *> top' /\
    downRect tm L0 L' w width /\
    P L' top') ->
  P L top ->
  leftRealizes tm h L l ->
  ~halts tm (l {{{ (h,R) }}} top).
Proof.
  intros Hstep HP Hleft.
  eapply quadRect_nonhalt.
  - eapply downRect_inf_concat; eauto.
  - exact Hleft.
Qed.

Arguments sideS_n {tm} H r n.

End InfiniteRectInternal.

Definition downRect tm (L R : Stream (DH0*DH0)) (w : list Sym) (width : nat) :=
  @InfiniteRectInternal.downRect tm L R w width.
Definition quadRect tm (L : Stream (DH0*DH0)) (top : side) :=
  @InfiniteRectInternal.quadRect tm L top.
Definition leftRealizes tm (h : DH0) (L : Stream (DH0*DH0)) (l : side) :=
  @InfiniteRectInternal.leftRealizes tm h L l.
Definition segRLs_n1_c tm (ls1 ls2:list (DH0*DH0)) (w1 w2:list Sym) (T:nat) :=
  @InfiniteRectInternal.segRLs_n1_c tm ls1 ls2 w1 w2 T.

Lemma segRLs_n1_c_spec tm ls1 ls2 w1 w2 T:
  segRLs_n1_c tm ls1 ls2 w1 w2 T = true ->
  segRLs_n tm ls1 ls2 w1 w2 1.
Proof.
  exact (InfiniteRectInternal.segRLs_n1_c_spec tm ls1 ls2 w1 w2 T).
Qed.

Ltac solve_segRLs_n1_with bound :=
  eapply (segRLs_n1_c_spec _ _ _ _ _ bound); vm_compute; reflexivity.

Ltac solve_segRLs_n1 :=
  first [
    let bound := constr:(1000) in solve_segRLs_n1_with bound
  | solve_segRLs_n
  ].

Lemma segRLs_n_downRect_trans tm hL hR L R w1 w2 width:
  segRLs_n tm hL hR w1 w2 width ->
  downRect tm L R w2 width ->
  downRect tm (hL *> L) (hR *> R) w1 width.
Proof.
  exact (InfiniteRectInternal.segRLs_n_downRect_trans tm hL hR L R w1 w2 width).
Qed.

Lemma segRLs_n_inf_trans tm L R w width
  (P : Stream (DH0*DH0) -> Stream (DH0*DH0) -> list Sym -> Prop):
  (forall L0 R0 top, P L0 R0 top -> exists hL hR bot L' R',
    O < length hR /\
    L0 = hL *> L' /\
    R0 = hR *> R' /\
    segRLs_n tm hL hR top bot width /\
    P L' R' bot) ->
  P L R w ->
  downRect tm L R w width.
Proof.
  exact (InfiniteRectInternal.segRLs_n_inf_trans tm L R w width P).
Qed.

Lemma downRect_quadRect_concat tm L R w width top:
  downRect tm L R w width ->
  quadRect tm R top ->
  quadRect tm L (w *> top).
Proof.
  exact (InfiniteRectInternal.downRect_quadRect_concat tm L R w width top).
Qed.

Lemma downRect_inf_concat tm L top
  (P : Stream (DH0*DH0) -> side -> Prop):
  (forall L0 top0, P L0 top0 -> exists L' top' w width,
    O < width /\
    top0 = w *> top' /\
    downRect tm L0 L' w width /\
    P L' top') ->
  P L top ->
  quadRect tm L top.
Proof.
  exact (InfiniteRectInternal.downRect_inf_concat tm L top P).
Qed.

Lemma leftRealizes_inf_concat tm h L l
  (P : DH0 -> Stream (DH0*DH0) -> side -> Prop):
  (forall h0 L0 l0, P h0 L0 l0 -> exists hs L' h' ls l',
    O < length hs /\
    L0 = hs *> L' /\
    lcons h0 ls = (hs,h') /\
    sideRLs (flip tm) ls l0 l' /\
    P h' L' l') ->
  P h L l ->
  leftRealizes tm h L l.
Proof.
  exact (InfiniteRectInternal.leftRealizes_inf_concat tm h L l P).
Qed.

Lemma sideRLs_leftRealizes_trans tm h hs L l h' ls l':
  lcons h ls = (hs,h') ->
  sideRLs (flip tm) ls l l' ->
  leftRealizes tm h' L l' ->
  leftRealizes tm h (hs *> L) l.
Proof.
  exact (InfiniteRectInternal.sideRLs_leftRealizes_trans tm h hs L l h' ls l').
Qed.

Lemma quadRect_nonhalt tm L top h l:
  quadRect tm L top ->
  leftRealizes tm h L l ->
  ~halts tm (l {{{ (h,R) }}} top).
Proof.
  exact (InfiniteRectInternal.quadRect_nonhalt tm L top h l).
Qed.

Opaque downRect quadRect leftRealizes.
