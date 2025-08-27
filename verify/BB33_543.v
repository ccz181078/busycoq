(** * Unofficial holdout ID 543 1RB2LA1LC_1LA2RB1RB_---2LB0LC *)
(** Coq proof by mxdys. Proof sketch by dyuan01. *)

From BusyCoq Require Import Individual33.
From Coq Require Import PeanoNat ZArith ZifyNat Lia String List.

Definition tm := Eval compute in (TM_from_str "1RB2LA1LC_1LA2RB1RB_---2LB0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation cRL := [((B,[]),(C,[]))].
Notation aRL := [((B,[]),(A,[]))].
Notation cLR := [((C,[]),(B,[]))].
Notation aLR := [((A,[]),(B,[]))].

Inductive Tp := _a | _c.

Definition Lmp(x:Tp):list (DH0*DH0) :=
match x with
| _a => aLR
| _c => cLR
end.

Definition Rmp(x:Tp):list (DH0*DH0) :=
match x with
| _a => aRL
| _c => cRL
end.

Notation "a ^^^ b" := (flat_map a b) (at level 20).

Definition P n h :=
  forall r,
  sideRLs tm (Rmp^^^h) ([0]^^n*>r) ([1]^^n*>r).

Lemma P_0:
  P 0 [].
Proof.
  unfold P.
  intros.
  solve_sideRLs.
Qed.

Lemma P_1:
  P 1 [_a].
Proof.
  unfold P.
  intros.
  solve_sideRLs.
Qed.

Lemma P_S n h1 h2:
  P n h1 ->
  P (1+n) h2 ->
  P (2+n) (h2++[_c]++h1).
Proof.
  unfold P.
  repeat rewrite flat_map_app.
  intros HP1 HP2 r.
  eapply sideRLs_trans.
  1: applys_eq (HP2 ([0]*>r)); simpl_rotate; reflexivity.
  eapply sideRLs_trans.
  2: applys_eq (HP1 ([1;1]*>r)); simpl_rotate; reflexivity.
  solve_sideRLs.
Qed.

Inductive P': nat->list Tp->Prop :=
| P'_0: P' 0 [_c]
| P'_1: P' 1 [_a;_c]
| P'_2 n h1 h2:
  P' n h1 ->
  P' (1+n) h2 ->
  P' (2+n) (h2++h1)
.

Lemma P'_spec n h:
  P' n h ->
  exists h',
  h=h'++[_c] /\
  P n h'.
Proof.
  intros H.
  induction H.
  - eexists []; split.
    2: apply P_0.
    reflexivity.
  - eexists [_a]; split.
    2: apply P_1.
    reflexivity.
  - destruct IHP'1 as [h'1 [I1 I2]].
    destruct IHP'2 as [h'2 [I3 I4]].
    subst.
    eexists; split.
    2: apply P_S; eassumption.
    repeat rewrite app_assoc.
    reflexivity.
Qed.

Definition RC n := [0]^^n *> [1;1] *> 0inf.

Lemma RIncs n h:
  P' n h ->
  sideRLs tm (Rmp^^^(h)) (RC n) (RC (1+n)).
Proof.
  intros HP'.
  apply P'_spec in HP'.
  destruct HP' as [h' [I1 HP]].
  subst.
  unfold RC.
  rewrite flat_map_app.
  eapply sideRLs_trans.
  1: apply HP.
  solve_sideRLs.
Qed.



Notation ld1 := <[2;1].
Notation ld0 := <[1;1].

Inductive LC0: nat->nat->(list Sym)->Prop :=
| LC0_O:
    LC0 0 0 []
| LC0_S0 len k x:
    LC0 len k x ->
    LC0 (1+len) (2^len-1-k) (ld1<+x)
| LC0_S1 len k x:
    LC0 len k x ->
    LC0 (1+len) (2^len+k) (ld0<+x).

Lemma LC0_lt [len k x]:
  LC0 len k x ->
  k<2^len.
Proof.
  intros.
  induction H; cbn; lia.
Qed.

Lemma LC0_ex len k:
  k<2^len ->
  exists x, LC0 len k x.
Proof.
  gen k.
  induction len; intros.
  - replace k with O by lia.
    eexists; econstructor.
  - cbn in H.
    assert (k<2^len\/2^len<=k) as [E|E] by lia.
    + epose proof (IHlen (2^len-1-k) _) as [x I1].
      eexists.
      applys_eq (LC0_S0 _ _ _ I1).
      lia.
    + epose proof (IHlen (k-2^len) _) as [x I1].
      eexists.
      applys_eq (LC0_S1 _ _ _ I1).
      lia.
  Unshelve.
  all: lia.
Qed.

Lemma LC0_max len x:
  LC0 (len) (2^(len)-1) x -> x = (ld0^^(len)).
Proof.
  gen x.
  induction len; intros.
  + inverts H.
    reflexivity.
  + cbn[Nat.pow] in *.
    inverts H.
    1: lia.
    replace k with (2^len-1) in * by lia.
    apply IHlen in H2.
    subst.
    rewrite <-Nat.add_1_r,lpow_add.
    reflexivity.
Qed.

Lemma LC0_min len x:
  LC0 (1+len) 0 x -> x = (ld1<+ld0^^len).
Proof.
  intros H.
  inverts H.
  2: lia.
  epose proof (LC0_lt H2).
  replace k with (2^len-1) in * by lia.
  apply LC0_max in H2.
  subst.
  reflexivity.
Qed.

Lemma LC0_Inc [len k x x']:
  LC0 len k x ->
  LC0 len (k+1) x' ->
  ((k mod 2 = 0%nat ->
  segRLs tm' cLR [] x x' /\
  segRLs tm' cLR [] x' x) /\
  (k mod 2 = 1%nat ->
  segRLs tm' aLR [] x x' /\
  segRLs tm' aLR [] x' x)).
Proof.
  gen k x x'.
  induction len; intros.
  - inverts H0.
    lia.
  - cbn in H.
    assert (k<2^len-1\/k=2^len-1\/2^len<=k) as [E|[E|E]] by lia.
    + inverts H.
      2: lia.
      inverts H0.
      2: lia.
      epose proof (LC0_lt H2).
      replace k0 with (k+1) in * by lia.
      epose proof (IHlen _ _ _ H3 H2) as [I1 I2].
      destruct len.
      1: lia.
      split; intro; cbn[Nat.pow] in *.
      * unshelve epose proof (I1 _) as [I1a I1b].
        1: lia.
        split;
        (eapply segRLs_concat; [ eassumption | ]; constructor).
      * unshelve epose proof (I2 _) as [I2a I2b].
        1: lia.
        split;
        (eapply segRLs_concat; [ eassumption | ]; constructor).
    + subst.
      inverts H.
      2: lia.
      inverts H0.
      1: lia.
      replace k0 with O in * by lia.
      epose proof (LC0_lt H3).
      replace k with O in * by lia.
      destruct len.
      * inverts H3.
        inverts H4.
        split; intro; [|lia]; split; solve_segRLs.
      * apply LC0_min in H3,H4.
        subst.
        cbn[Nat.pow].
        split; intro; [lia|]; split; solve_segRLs.
    + inverts H.
      1: lia.
      inverts H0.
      1: lia.
      epose proof (LC0_lt H3).
      replace k with (k0+1) in * by lia.
      epose proof (IHlen _ _ _ H2 H3) as [I1 I2].
      destruct len.
      1: lia.
      split; intro; cbn[Nat.pow] in *.
      * unshelve epose proof (I1 _) as [I1a I1b].
        1: lia.
        split;
        (eapply segRLs_concat; [ eassumption | ]; constructor).
      * unshelve epose proof (I2 _) as [I2a I2b].
        1: lia.
        split;
        (eapply segRLs_concat; [ eassumption | ]; constructor).
Qed.

Inductive LC: nat->nat->side->Prop :=
| LC_O m:
  LC m 0 (0inf<*[1]^^m)
| LC_S len k x m:
  LC0 len k x ->
  len*2+2<=m ->
  LC m (2^len+k) (0inf<*[1]^^(m-(len*2+2))<*ld1<*x).

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  rw_pa.

Lemma LC_Inc m n x x':
  LC m n x ->
  LC m (n+1) x' ->
  ((n mod 2 = 0%nat ->
  sideRLs tm' cLR x x' /\
  sideRLs tm' cLR x' x) /\
  (n mod 2 = 1%nat ->
  sideRLs tm' aLR x x' /\
  sideRLs tm' aLR x' x)).
Proof.
  intros.
  inverts H.
  - inverts H0.
    replace k with O in * by lia.
    destruct len; cbn[Nat.pow] in *.
    2: lia.
    inverts H1.
    split; intro; [|lia].
    cbn.
    remember (m-2) as m'.
    replace m with (2+m') in * by lia.
    split; solve_sideRLs.
  - inverts H0.
    1: lia.
    epose proof (LC0_lt H1).
    epose proof (LC0_lt H3).
    assert (len0<len\/len0>len+1\/len0=len\/len0=len+1) as [E|[E|[E|E]]] by lia.
    + pp_pow2_lt_le len0 len.
      lia.
    + pp_pow2_lt_le (len+1) len0.
      lia.
    + subst.
      replace k0 with (k+1) in * by lia.
      destruct len.
      1: lia.
      cbn[Nat.pow] in *.
      epose proof (LC0_Inc H1 H3) as [I1 I2].
      split; intro.
      * unshelve epose proof (I1 _) as [I1a I1b]; [lia|].
        split;
        (eapply segRLs_sideRLs_concat; [eassumption|]; constructor).
      * unshelve epose proof (I2 _) as [I2a I2b]; [lia|].
        split;
        (eapply segRLs_sideRLs_concat; [eassumption|]; constructor).
    + subst.
      rw_pa.
      replace k0 with O in * by lia.
      replace k with (2^len-1) in * by lia.
      split; intro.
      1: lia.
      rewrite Nat.add_comm in H3.
      apply LC0_min in H3.
      apply LC0_max in H1.
      subst.
      remember (m-((len+1)*2+2)) as m'.
      replace (m-((len)*2+2)) with (2+m') by lia.
      split; solve_sideRLs.
Qed.

Lemma LC_Ov m x x':
  LC m 0 x ->
  LC (1+m) 0 x' ->
  sideRLs tm' aLR x x'.
Proof.
  intros.
  inverts H.
  2: lia.
  inverts H0.
  2: lia.
  solve_sideRLs.
Qed.

Lemma highbit n:
  n<>O ->
  exists len m2, n = 2^len + m2 /\ m2 < 2^len.
Proof.
  induction n using Wf_nat.lt_wf_ind.
  intros.
  assert (n=n/2*2+n mod 2) by lia.
  remember (n/2) as n1.
  remember (n mod 2) as n2.
  assert (n=1\/n1<>0)%nat as [E|E] by lia.
  1: exists O,O; cbn; lia.
  unshelve epose proof (H n1 _ _) as [len [m2 I1]].
  1,2: lia.
  exists (1+len),(m2*2+n2).
  cbn; lia.
Qed.

Lemma LC_ex m k:
  k<2^(m/2) ->
  exists x, LC m k x.
Proof.
  intros H.
  destruct k.
  - eexists.
    constructor.
  - unshelve epose proof (highbit (S k) _) as [len [k0 [I1 I2]]].
    1: lia.
    epose proof (LC0_ex _ _ I2) as [x I3].
    assert (len*2+2<=m) as I5 by (pp_pow2_lt_le len (m/2); lia).
    epose proof (LC_S _ _ _ _ I3 I5) as I4.
    rewrite <-I1 in I4.
    eexists.
    apply I4.
Qed.
 
Inductive LC': nat->Z->side->Prop :=
| LC'_0 m n x:
  LC (m*2) n x ->
  LC' m (Z.of_nat n) x
| LC'_1 m n x:
  LC (m*2+1) n x ->
  LC' m (-(Z.of_nat n+1)) x
.

Lemma LC'_ex m k:
  (-(Z.of_nat (2^m))<=k<Z.of_nat (2^m))%Z ->
  exists x, LC' m k x.
Proof.
  intros.
  assert (k<0\/0<=k)%Z as [E|E] by lia.
  - epose proof (LC_ex _ _ _) as [x I1].
    eexists.
    applys_eq (LC'_1 (m) (Z.to_nat (-1-k))).
    1: lia.
    apply I1.
    Unshelve.
    replace ((m*2+1)/2) with (m) by lia.
    lia.
  - epose proof (LC_ex _ _ _) as [x I1].
    eexists.
    applys_eq (LC'_0 (m) (Z.to_nat (k))).
    1: lia.
    apply I1.
    Unshelve.
    replace ((m*2)/2) with (m) by lia.
    lia.
Qed.

Local Opaque Z.sub.

Lemma LC'_Inc m n x x':
  (LC' m n x ->
  LC' m (n+1) x' ->
  n<>-1 ->
  ((n mod 2 = 0 ->
  sideRLs tm' cLR x x' /\
  sideRLs tm' cLR x' x) /\
  (n mod 2 = 1 ->
  sideRLs tm' aLR x x' /\
  sideRLs tm' aLR x' x)))%Z.
Proof.
  intros.
  inverts H0.
  - inverts H.
    2: lia.
    replace n0 with (n1+1) in * by lia.
    epose proof (LC_Inc _ _ _ _ H0 H4) as [I1 I2].
    split; intro.
    * apply I1; lia.
    * apply I2; lia.
  - inverts H.
    1: lia.
    replace n1 with (n0+1) in * by lia.
    epose proof (LC_Inc _ _ _ _ H4 H0) as [I1 I2].
    split; intro.
    * split; apply I1; lia.
    * split; apply I2; lia.
Qed.

Lemma LC'_Ov m x x':
  LC' m (-1) x ->
  LC' (1+m) 0 x' ->
  sideRLs tm' aLR x x'.
Proof.
  intros.
  inverts H.
  1: lia.
  inverts H0.
  2: lia.
  replace n with O in * by lia.
  replace n0 with O in * by lia.
  eapply LC_Ov.
  1: apply H3.
  applys_eq H4; lia.
Qed.

Lemma LC'_Ov' m x x':
  LC' m (-1) x ->
  LC' m 0 x' ->
  sideRLs tm' aLR x' x.
Proof.
  intros.
  inverts H.
  1: lia.
  inverts H0.
  2: lia.
  replace n with O in * by lia.
  replace n0 with O in * by lia.
  eapply LC_Ov.
  1: apply H4.
  applys_eq H3; lia.
Qed.

Local Transparent Z.sub.

Fixpoint LIncs(ls:list Tp)(s:Z)(a:nat):Z*nat :=
(match ls with
| [] => (s,a)
| _a::t =>
  if s mod 2 =? 0 then
    LIncs t (s-1) a
  else
    LIncs t (s+1) (if s=?-1 then 1+a else a)
| _c::t =>
  if s mod 2 =? 0 then
    LIncs t (s+1) a
  else
    LIncs t (s-1) a
end)%Z.

Lemma LIncs_spec ls s a x:
  LC' a s x ->
  (let '(s0,a0):=LIncs ls s a in
  s+(Z.of_nat (length ls))<2^(Z.of_nat a) ->
  s-(Z.of_nat (length ls))>-2^(Z.of_nat a) ->
  exists x',
  LC' a0 s0 x' /\
  sideRLs tm' (Lmp^^^ls) x x')%Z.
Proof.
  gen s a x.
  induction ls; cbn[LIncs]; intros.
  - eexists; split.
    1: apply H.
    constructor.
  - destruct a.
    + destruct (Z.eqb_spec (s mod 2) 0).
      * destruct (LIncs ls (s-1) a0) as [s' a'] eqn:E.
        destruct (Z.eqb_spec s 0).
        {
          cbn[length].
          intros.
          subst.
          unshelve epose proof (LC'_ex a0 (-1) _) as [x' I1]; [lia|].
          epose proof (LC'_Ov' _ _ _ I1 H) as I2.
          epose proof (IHls _ _ _ I1) as IHls.
          cbn in E.
          rewrite E in IHls.
          unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
          cbn[flat_map].
          eexists; split; [ apply I3 |].
          eapply sideRLs_trans; eassumption.
        }
        {
          cbn[length].
          intros.
          unshelve epose proof (LC'_ex a0 (s-1) _) as [x' I1]; [lia|].
          unshelve epose proof (LC'_Inc _ _ _ _ I1 _ _) as [_ I2].
          2: applys_eq H; lia.
          1: lia.
          epose proof (IHls _ _ _ I1) as IHls.
          rewrite E in IHls.
          unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
          cbn[flat_map].
          eexists; split; [ apply I3 |].
          eapply sideRLs_trans; [apply I2; lia|eassumption].
        }
      * destruct (Z.eqb_spec s (-1)).
        {
          destruct (LIncs ls (s+1) (1+a0)) as [s' a'] eqn:E.
          cbn[length].
          intros.
          subst.
          unshelve epose proof (LC'_ex (1+a0) 0 _) as [x' I1]; [lia|].
          epose proof (LC'_Ov _ _ _ H I1) as I2.
          epose proof (IHls _ _ _ I1) as IHls.
          rewrite Nat2Z.inj_add in IHls.
          rewrite Z.pow_add_r in IHls by lia.
          cbn[Nat.add] in *.
          cbn in E.
          rewrite E in IHls.
          unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
          cbn[flat_map].
          eexists; split; [ apply I3 |].
          eapply sideRLs_trans; eassumption.
        }
        {
          destruct (LIncs ls (s+1) (a0)) as [s' a'] eqn:E.
          cbn[length].
          intros.
          unshelve epose proof (LC'_ex a0 (s+1) _) as [x' I1]; [lia|].
          unshelve epose proof (LC'_Inc _ _ _ _ H I1 _) as [_ I2].
          1: lia.
          epose proof (IHls _ _ _ I1) as IHls.
          rewrite E in IHls.
          unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
          cbn[flat_map].
          eexists; split; [ apply I3 |].
          eapply sideRLs_trans; [apply I2; lia|eassumption].
        }
    + destruct (Z.eqb_spec (s mod 2) 0).
      * destruct (LIncs ls (s+1) (a0)) as [s' a'] eqn:E.
        cbn[length].
        intros.
        unshelve epose proof (LC'_ex a0 (s+1) _) as [x' I1]; [lia|].
        unshelve epose proof (LC'_Inc _ _ _ _ H I1 _) as [I2 _].
        1: lia.
        epose proof (IHls _ _ _ I1) as IHls.
        rewrite E in IHls.
        unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
        cbn[flat_map].
        eexists; split; [ apply I3 |].
        eapply sideRLs_trans; [apply I2; lia|eassumption].
      * destruct (LIncs ls (s-1) (a0)) as [s' a'] eqn:E.
        cbn[length].
        intros.
        unshelve epose proof (LC'_ex a0 (s-1) _) as [x' I1]; [lia|].
        unshelve epose proof (LC'_Inc _ _ _ _ I1 _ _) as [I2 _].
        2: applys_eq H; lia.
        1: lia.
        epose proof (IHls _ _ _ I1) as IHls.
        rewrite E in IHls.
        unshelve epose proof (IHls _ _) as [x'0 [I3 I4]]; [lia|lia|].
        cbn[flat_map].
        eexists; split; [ apply I3 |].
        eapply sideRLs_trans; [apply I2; lia|eassumption].
Qed.

Fixpoint LIncs0(ls:list Tp)(s:Z):Z :=
(match ls with
| [] => s
| _a::t =>
  if s mod 2 =? 0 then
    LIncs0 t (s-1)
  else
    LIncs0 t (s+1) 
| _c::t =>
  if s mod 2 =? 0 then
    LIncs0 t (s+1)
  else
    LIncs0 t (s-1)
end)%Z.

Lemma LIncs0_spec ls s a:
  LIncs0 ls s = fst (LIncs ls s a).
Proof.
  gen s a.
  induction ls; cbn; intros.
  1: trivial.
  destruct a; destruct (s mod 2 =? 0)%Z; rewrite <-IHls; reflexivity.
Qed.

Lemma LIncs0_rev ls s:
  (LIncs0 ls (-s-1) = -LIncs0 ls s-1)%Z.
Proof.
  gen s.
  induction ls; cbn; intros.
  1: trivial.
  destruct a; destruct (Z.eqb_spec ((-s-1) mod 2) 0); destruct (Z.eqb_spec (s mod 2) 0); try lia.
  1,4: applys_eq (IHls (s+1)%Z); f_equal; lia.
  1,2: applys_eq (IHls (s-1)%Z); f_equal; lia.
Qed.

Lemma LIncs0_mod2 ls s s':
  ((s mod 2 = s' mod 2) ->
  (LIncs0 ls s)-s = (LIncs0 ls s')-s')%Z.
Proof.
  gen s s'.
  induction ls; cbn; intros.
  1: lia.
  rewrite <-H.
  destruct a; destruct (Z.eqb_spec (s mod 2) 0).
  1,4: specialize (IHls (s-1) (s'-1))%Z; lia.
  1,2: specialize (IHls (s+1) (s'+1))%Z; lia.
Qed.

Lemma LIncs0_trans ls1 ls2 s:
  LIncs0 (ls1++ls2) s =
  (LIncs0 ls2 (LIncs0 ls1 s)).
Proof.
  gen s.
  induction ls1; cbn; intros.
  1: trivial.
  destruct a; destruct (Z.eqb_spec (s mod 2) 0); apply IHls1.
Qed.

Definition LIncs1 ls := LIncs0 ls 0.

Lemma LIncs1_0 ls s:
  (s mod 2 = 0 ->
  LIncs0 ls s = s+LIncs1 ls)%Z.
Proof.
  unfold LIncs1.
  epose proof (LIncs0_mod2 ls s 0).
  lia.
Qed.

Lemma LIncs1_1 ls s:
  (s mod 2 = 1 ->
  LIncs0 ls s = s-LIncs1 ls)%Z.
Proof.
  unfold LIncs1.
  epose proof (LIncs0_mod2 ls s (-1)).
  epose proof (LIncs0_rev ls 0).
  cbn in H0.
  lia.
Qed.

Lemma LIncs1_trans ls1 ls2:
  (LIncs1 (ls1++ls2) = (LIncs1 ls1)+(1-((LIncs1 ls1) mod 2)*2)*(LIncs1 ls2))%Z.
Proof.
  destruct (Z.eqb_spec ((LIncs1 ls1) mod 2) 0).
  - epose proof (LIncs1_0 ls2 (LIncs1 ls1)).
    unfold LIncs1 in *.
    rewrite LIncs0_trans.
    lia.
  - epose proof (LIncs1_1 ls2 (LIncs1 ls1)).
    unfold LIncs1 in *.
    rewrite LIncs0_trans.
    replace (LIncs0 ls1 0 mod 2)%Z with 1%Z by lia.
    lia.
Qed.

Lemma LIncs1_P' n x:
  P' n x ->
  LIncs1 x =
  match n mod 6 with
  | 1%nat => (-2)%Z
  | 2%nat => (-1)%Z
  | 4 => 2%Z
  | 5 => 3%Z
  | _ => 1%Z
  end.
Proof.
  intros.
  induction H.
  1,2: reflexivity.
  remember (n mod 6) as v1.
  replace ((1+n) mod 6) with ((1+v1) mod 6) in * by lia.
  replace ((2+n) mod 6) with ((2+v1) mod 6) in * by lia.
  rewrite LIncs1_trans,IHP'2,IHP'1.
  clear IHP'2 IHP'1.
  do 6
  (destruct v1;
  [ reflexivity |]).
  lia.
Qed.

Fixpoint LIncs_a(ls:list Tp)(s:Z):nat :=
(match ls with
| [] => O
| _a::t =>
  if s mod 2 =? 0 then
    LIncs_a t (s-1)
  else
    if s=?-1 then
      S (LIncs_a t (s+1))
    else
      LIncs_a t (s+1)
| _c::t =>
  if s mod 2 =? 0 then
    LIncs_a t (s+1)
  else
    LIncs_a t (s-1)
end)%Z.

Lemma LIncs_a_spec ls s a:
  a + LIncs_a ls s = snd (LIncs ls s a).
Proof.
  gen s a.
  induction ls; cbn; intros.
  1: lia.
  destruct a; destruct (s mod 2 =? 0)%Z; rewrite <-IHls; try lia.
  destruct (s=?-1)%Z; lia.
Qed.

Lemma LIncs_spec' ls s a:
  LIncs ls s a = ((s+(1-(s mod 2)*2)*(LIncs1 ls))%Z,a+LIncs_a ls s).
Proof.
  rewrite LIncs_a_spec.
  epose proof (LIncs0_spec ls s a).
  epose proof (LIncs1_0 ls s).
  epose proof (LIncs1_1 ls s).
  assert ((s mod 2)=0\/(s mod 2)=1)%Z as [E|E] by lia; rewrite E in *;
  destruct (LIncs ls s a) eqn:E0; f_equal; cbn in H; lia.
Qed.

Lemma lcons_Lmp ls:
  lcons (B,[]) (Lmp^^^ls) = (Rmp^^^ls,(B,[])).
Proof.
  induction ls.
  1: reflexivity.
  destruct a; cbn; rewrite IHls; reflexivity.
Qed.

Definition S0 (a:side*nat) :=
  let '(x,i):=a in
  x {{B}}> RC i.

Lemma BigStep a s x i ls:
  LC' a s x ->
  P' i ls ->
  (Z.abs s + Z.of_nat (length ls) < 2^Z.of_nat a)%Z ->
  exists x',
  LC' (a+LIncs_a ls s) ((s+(1-(s mod 2)*2)*(LIncs1 ls))%Z)%Z x' /\
  S0 (x,i) -->+ S0 (x',1+i).
Proof.
  unfold S0.
  intros HLC' HP' Hlt.
  epose proof (LIncs_spec _ _ _ _ HLC') as I1.
  rewrite LIncs_spec' in I1.
  epose proof (I1 _ _) as [x' [I2 I3]].
  eexists; split.
  1: apply I2.
  epose proof HP' as I4.
  apply RIncs in I4.
  eapply (sideRLs_concat_v2 (lcons_Lmp _) _ I3 I4).
  Unshelve.
  1,2: lia.
  apply P'_spec in HP'.
  destruct HP' as [h' [I5 I6]].
  subst.
  rewrite flat_map_app.
  intros X.
  epose proof (@f_equal _ _ (@length _) _ _ X) as X0.
  rewrite length_app in X0; cbn in X0; lia.
Qed.

Lemma P'_n n:
  exists x, P' n x.
Proof.
  induction n using Wf_nat.lt_wf_ind.
  destruct n as [|[|n]].
  - eexists; constructor.
  - eexists; constructor.
  - epose proof (H n _) as [x1 I1].
    epose proof (H (S n) _) as [x2 I2].
    eexists; econstructor; eassumption.
  Unshelve.
  all: lia.
Qed.

Lemma P'_unique [n x x']:
  P' n x ->
  P' n x' ->
  x = x'.
Proof.
  gen x x'.
  induction n using Wf_nat.lt_wf_ind; intros.
  destruct n as [|[|n]]; inverts H0; inverts H1; trivial.
  epose proof (H _ _ _ _ H3 H2).
  epose proof (H _ _ _ _ H4 H5).
  subst; trivial.
  Unshelve.
  all: lia.
Qed.

Lemma P'_prefix i i0 x x0:
  0<i<=i0 ->
  P' i x ->
  P' i0 x0 ->
  exists x1, x0 = x++x1.
Proof.
  intro.
  assert (0<i<i0\/i=i0) as [E|E] by lia.
  2: {
    subst.
    intros.
    epose proof (P'_unique H0 H1).
    subst.
    eexists [].
    rewrite app_nil_r.
    reflexivity.
  }
  clear H.
  rename E into H.
  intros.
  gen x0 H H1.
  induction i0; intros.
  1: lia.
  inverts H1.
  1: lia.
  assert (i<S n\/i=S n) as [E|E] by lia.
  - epose proof (IHi0 _ _ H4) as [x1 I1].
    subst.
    eexists.
    rewrite app_assoc; reflexivity.
  - subst.
    epose proof (P'_unique H0 H4).
    subst.
    eexists; reflexivity.
  Unshelve.
  lia.
Qed.

Lemma LIncs_a_mono ls1 ls2 s:
  LIncs_a ls1 s <= LIncs_a (ls1++ls2) s.
Proof.
  gen ls2 s.
  induction ls1; intros; cbn.
  1: lia.
  destruct a; destruct (s mod 2 =? 0)%Z.
  2: destruct (s=?-1)%Z.
  2: specialize (IHls1 ls2 (s+1)%Z); lia.
  all: apply IHls1.
Qed.

Ltac inv_P' :=
  repeat
  match goal with
  | [H:P' _ _ |- _] => inverts H
  end.

Lemma length_P' i x:
  P' (4+i) x ->
  length x <= 2^i*8.
Proof.
  gen x.
  induction i using Wf_nat.lt_wf_ind; intros.
  inverts H0.
  destruct i as [|[|i]].
  - inv_P'.
    cbn; lia.
  - inv_P'.
    cbn; lia.
  - epose proof (H _ _ _ H2).
    epose proof (H _ _ _ H3).
    cbn[Nat.pow] in *.
    rewrite length_app.
    lia.
  Unshelve.
  all: lia.
Qed.

Lemma LIncs_a_7_0 x:
  P' 7 x ->
  LIncs_a x 0 = 2%nat.
Proof.
  intros HP'.
  inv_P'.
  vm_compute; reflexivity.
Qed.

Lemma BigStep_7 m x i:
  LC' m 0 x ->
  i*6+7<=m ->
  exists m' x',
  LC' m' (-2) x' /\
  i*6+9<=m' /\
  S0 (x,i*6+7) -->+ S0 (x',i*6+8).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+7)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+3) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+6) m; lia.
  epose proof (P'_n 7) as [x0 HP'0].
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+7) mod 6) with 1%nat in I1 by lia.
  unshelve epose proof (P'_prefix _ _ _ _ _ HP'0 HP') as [x1 I3].
  1: lia.
  subst.
  epose proof (LIncs_a_mono x0 x1 0) as Hmono.
  cbn in I1.
  rewrite LIncs_a_7_0 in Hmono by (apply HP'0).
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Lemma LIncs_a_7_neg2 x:
  P' 7 x ->
  LIncs_a x (-2) = 3%nat.
Proof.
  intros HP'.
  inv_P'.
  vm_compute; reflexivity.
Qed.

Lemma BigStep_8 m x i:
  LC' m (-2) x ->
  i*6+9<=m ->
  exists m' x',
  LC' m' (-3) x' /\
  i*6+12<=m' /\
  S0 (x,i*6+8) -->+ S0 (x',i*6+9).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+8)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+4) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+7) m; lia.
  epose proof (P'_n 7) as [x0 HP'0].
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+8) mod 6) with 2%nat in I1 by lia.
  unshelve epose proof (P'_prefix _ _ _ _ _ HP'0 HP') as [x1 I3].
  1: lia.
  subst.
  epose proof (LIncs_a_mono x0 x1 (-2)) as Hmono.
  cbn in I1.
  rewrite LIncs_a_7_neg2 in Hmono by (apply HP'0).
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Lemma LIncs_a_7_neg3 x:
  P' 7 x ->
  LIncs_a x (-3) = O.
Proof.
  intros HP'.
  inv_P'.
  vm_compute. reflexivity.
Qed.

Lemma BigStep_9 m x i:
  LC' m (-3) x ->
  i*6+12<=m ->
  exists m' x',
  LC' m' (-4) x' /\
  i*6+12<=m' /\
  S0 (x,i*6+9) -->+ S0 (x',i*6+10).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+9)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+5) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+8) m; lia.
  epose proof (P'_n 7) as [x0 HP'0].
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+9) mod 6) with 3%nat in I1 by lia.
  unshelve epose proof (P'_prefix _ _ _ _ _ HP'0 HP') as [x1 I3].
  1: lia.
  subst.
  epose proof (LIncs_a_mono x0 x1 (-3)) as Hmono.
  cbn in I1.
  rewrite LIncs_a_7_neg3 in Hmono by (apply HP'0).
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Lemma LIncs_a_7_neg4 x:
  P' 7 x ->
  LIncs_a x (-4) = 1%nat.
Proof.
  intros HP'.
  inv_P'.
  vm_compute. reflexivity.
Qed.

Lemma BigStep_10 m x i:
  LC' m (-4) x ->
  i*6+12<=m ->
  exists m' x',
  LC' m' (-2) x' /\
  i*6+13<=m' /\
  S0 (x,i*6+10) -->+ S0 (x',i*6+11).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+10)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+6) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+9) m; lia.
  epose proof (P'_n 7) as [x0 HP'0].
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+10) mod 6) with 4%nat in I1 by lia.
  unshelve epose proof (P'_prefix _ _ _ _ _ HP'0 HP') as [x1 I3].
  1: lia.
  subst.
  epose proof (LIncs_a_mono x0 x1 (-4)) as Hmono.
  cbn in I1.
  rewrite LIncs_a_7_neg4 in Hmono by (apply HP'0).
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Lemma BigStep_11 m x i:
  LC' m (-2) x ->
  i*6+13<=m ->
  exists m' x',
  LC' m' 1 x' /\
  i*6+13<=m' /\
  S0 (x,i*6+11) -->+ S0 (x',i*6+12).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+11)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+7) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+10) m; lia.
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+11) mod 6) with 5%nat in I1 by lia.
  subst.
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Lemma BigStep_12 m x i:
  LC' m 1 x ->
  i*6+13<=m ->
  exists m' x',
  LC' m' 0 x' /\
  i*6+13<=m' /\
  S0 (x,i*6+12) -->+ S0 (x',i*6+13).
Proof.
  intros HLC' Hm.
  epose proof (P'_n (i*6+12)) as [ls HP'].
  unshelve epose proof (length_P' (i*6+8) ls _) as Hls.
  1: applys_eq HP'; lia.
  unshelve epose proof (BigStep _ _ _ _ _ HLC' HP' _) as [x' [I1 I2]].
  1: pp_pow2_lt_le (i*6+11) m; lia.
  erewrite LIncs1_P' in I1 by (apply HP').
  replace ((i*6+12) mod 6) with 0%nat in I1 by lia.
  subst.
  eexists _,_.
  split.
  1: apply I1.
  split.
  1: lia.
  follow10 I2.
  finish.
Qed.

Definition S1 '(x,i) := S0 (x,i*6+7).

Lemma init x:
  LC' 7 0 x ->
  c0 -->*
  S1 (x,O).
Proof.
  unfold S1,S0.
  intro.
  inverts H.
  2: lia.
  replace n with O in * by lia.
  inverts H2.
  2: lia.
  unfold RC.
  es.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  unshelve epose proof (LC'_ex 7 0 _) as [x I1].
  1: lia.
  eapply multistep_nonhalt.
  1: apply init,I1.
  eapply progress_nonhalt_cond with (P:=fun '(x,i)=> exists m, LC' m 0 x /\ i*6+7<=m).
  2: eexists; split; [apply I1|]; lia.
  clear x I1.
  intros [x i] [m [I1 I2]].
  epose proof (BigStep_7 _ _ _ I1 I2) as [m0 [x0 [I3 [I4 I5]]]].
  epose proof (BigStep_8 _ _ _ I3 I4) as [m1 [x1 [I6 [I7 I8]]]].
  epose proof (BigStep_9 _ _ _ I6 I7) as [m2 [x2 [I9 [I10 I11]]]].
  epose proof (BigStep_10 _ _ _ I9 I10) as [m3 [x3 [I12 [I13 I14]]]].
  epose proof (BigStep_11 _ _ _ I12 I13) as [m4 [x4 [I15 [I16 I17]]]].
  epose proof (BigStep_12 _ _ _ I15 I16) as [m5 [x5 [I18 [I19 I20]]]].
  eexists (_,S i).
  unfold S1.
  split.
  - follow11 I5.
    follow11 I8.
    follow11 I11.
    follow11 I14.
    follow11 I17.
    follow10 I20.
    finish.
  - eexists; split.
    1: apply I18.
    lia.
Qed.

