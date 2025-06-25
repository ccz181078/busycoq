From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import NatMod.
From BusyCoq Require Import SimplTape.

Open Scope list.

From BusyCoq Require Import Longitudinal.

Lemma lpow_rotate_list {A} (a0:list A) a1 b n:
  (a1::a0)^^n ++ a1::b = a1::(a0++[a1])^^n++b.
Proof.
  induction n; cbn.
  - trivial.
  - repeat rewrite <-app_assoc.
    rewrite IHn.
    trivial.
Qed.

Ltac solve_seg :=
  unfold segRL,segRR,segLL,segLR; intros; cbn;
  (eapply evstep_progress_trans || eapply evstep_trans);
  [ repeat (rewrite Str_app_assoc || cbn[Str_app]);
    simpl_tape;
    finish
  | ];
  (repeat (er; try sr)); finish;
  repeat rewrite Str_cons_def;
  repeat rewrite <-Str_app_assoc;
  cbn[app];
  reflexivity.

Ltac solve_segRLs :=
  repeat (
  (eapply segRLs_S; [solve_seg |]) ||
  (eapply segRLs_RR_LLs; [solve_seg |]) ||
  (eapply segLLs_LR_LLs; [solve_seg |]) ||
  (eapply segLLs_LL_RLs; [solve_seg |]) ||
  eapply segRLs_O ||
  rewrite lpow_add ||
  rewrite <-app_assoc ||
  rewrite lpow_rotate_list ||
  cbn[app]).

Ltac solve_sideRLs :=
  repeat (eapply sideRLseq_S;
  [ intros l;
    unfold to_DH_config; cbn;
    (repeat (er; try sr)) | ] ||
  eapply sideRLseq_O).

Lemma lt_mul2add1 a b:
  a<b ->
  a*2+1<b*2.
Proof. lia. Qed.

Lemma lt_mul2 a b:
  a<b ->
  a*2<b*2.
Proof. lia. Qed.

Lemma lt_pow2sub1 a:
  2^a-1<2^a.
Proof.
  pose proof (Nat.pow_nonzero 2 a).
  lia.
Qed.

Lemma lt_0_pow2 a:
  0<2^a.
Proof.
  pose proof (Nat.pow_nonzero 2 a).
  lia.
Qed.

Ltac solve_pow2_lt :=
  repeat (rewrite pow2_S || rewrite Nat.pow_add_r ||
  apply lt_pow2sub1 ||
  apply lt_0_pow2 ||
  apply lt_sub1 || apply lt_mul2add1 || apply lt_mul2 ||
  apply Nat.mul_lt_mono_pos_r).

Ltac follow00 I :=
  eapply evstep_trans; [ apply I | ].

Lemma segRLs_addmul tm a x b c h w1 w2:
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x+c)) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ c).
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Lemma segRLs_addmul' tm a x b c h w1 w2:
  x>=c ->
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^((x-c)*a+b)) (h^^x) w1 w2.
Proof.
  intros H.
  replace (h^^x) with (h^^(x-c+c)) by (f_equal; lia).
  apply segRLs_addmul.
Qed.

Lemma sub_add' a b:
  a>=b ->
  a = b+(a-b).
Proof.
  lia.
Qed.

Lemma Nat2N_ge a b:
  (N.of_nat a >= N.of_nat b)%N ->
  a>=b.
Proof. lia. Qed.

Ltac rw_nat_to_N :=
  repeat (
  rewrite Nnat.Nat2N.inj_add ||
  rewrite Nnat.Nat2N.inj_sub ||
  rewrite Nnat.Nat2N.inj_mul ||
  rewrite Nnat.Nat2N.inj_div ||
  rewrite Nnat.Nat2N.inj_mod ||
  rewrite Nnat.Nat2N.inj_pow ||
  rewrite Nnat.N2Nat.id).

Ltac solve_nat_eq_by_N :=
  apply Nnat.Nat2N.inj;
  rw_nat_to_N;
  reflexivity.

Ltac solve_nat_ge_by_N :=
  apply Nat2N_ge;
  rw_nat_to_N;
  unfold N.ge;
  vm_compute;
  congruence.

Inductive DivMod3: nat->Prop :=
| DivMod3_0 a: DivMod3 (0+a*3)
| DivMod3_1 a: DivMod3 (1+a*3)
| DivMod3_2 a: DivMod3 (2+a*3)
.

Lemma divmod3_cases a: DivMod3 a.
Proof.
  epose proof (Nat.Div0.div_mod a 3) as H.
  epose proof (Nat.mod_upper_bound a 3) as H0.
  destruct (a mod 3) as [|[|[|]]].
  - applys_eq (DivMod3_0 (a/3)); lia.
  - applys_eq (DivMod3_1 (a/3)); lia.
  - applys_eq (DivMod3_2 (a/3)); lia.
  - lia.
Qed.

Ltac divmod3 a :=
  epose proof (divmod3_cases a) as Hdm3;
  inverts Hdm3.

Lemma pow2_gt n: 2^n>n.
Proof.
  induction n; cbn; lia.
Qed.

Lemma mul1_ge a b c:
  a>=1 ->
  b>=c ->
  a*b>=c.
Proof.
  intros.
  replace a with (a-1+1) by lia.
  rewrite Nat.mul_add_distr_r.
  remember ((a-1)*b) as v1.
  lia.
Qed.

Lemma gt_ge_trans a b c:
  a>b -> b>=c -> a>=c.
Proof. lia. Qed.

Lemma ge_trans a b c:
  a>=b -> b>=c -> a>=c.
Proof. lia. Qed.

Lemma pow2_ge32 a:
  a>=5 ->
  2^a>=(a-5)*32.
Proof.
  remember (a-5) as v1.
  intros.
  replace a with (v1+5) by lia.
  rewrite Nat.pow_add_r.
  cbn.
  pose proof (pow2_gt v1).
  lia.
Qed.

Ltac solve_ge' :=
match goal with
| |- ?a + ?b >= ?c =>
  no_var b;
  eapply addc_ge; [ reflexivity | lia | ]
| |- ?a - ?b >= ?c =>
  no_var b;
  eapply subc_ge; [ reflexivity | ]
| |- ?a / ?b >= ?c =>
  no_var b;
  eapply divc_ge; [ reflexivity | congruence | ]
end.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RD1RB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (F,[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RE_0RD0LA_---1LB_1LE0RF_0RD1RB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (F,[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---1LB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (E,[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---1LC").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (E,[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RD_1LA0LA_1LF0RE_0RF1RB_---1LB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (E,[0]).
Notation hL := (C,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC1RE_---1LD_1LA0LA_1LE0RF_0RC1RB").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (F,[0]).
Notation hL := (D,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(A,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC0RA_1RB1LD_1LC0LC_1RF0LB_---1RE").

Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation d0 := <[1;0;1;1;1;1].
Notation d1 := <[1;1;1;1;1;1].
Notation d0' := <[1;0;1;1].
Notation w := <[1;0].
Notation w' := <[1;1].
Notation lh0 := (0inf<*[1]^^5).
Notation lh1 := (0inf<*[1]^^7).
Notation hR := (E,[1]).
Notation hL := (D,[1]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Lemma D_IncsOvs n m:
  segRLs tm (hRL^^((n+1)*2^m-1)) (hRL^^n) (d0^^m) (d1^^m).
Proof.
  eapply BC.IncsOvs.
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Lemma D_Ovs n m:
  segRLs tm (hRL^^(n*2^m)) (hRL^^n) (d1^^m) (d1^^m).
Proof.
  eapply BC.Ovs with (d0:=d0).
  1: solve_seg.
  1: solve_seg.
  1: solve_seg.
Qed.

Inductive LS :=
| W1(n:nat)(l:LS)
| W2(n:nat)(l:LS)
| H1 | H2 | H3 | H4 | H5.

Fixpoint Lmp(x:LS):side :=
match x with
| H1 => lh1
| H2 => (lh0<*(d0<+d1<+w'^^2))
| H3 => (lh0<*(d1<+w'^^2))
| H4 => (lh1<*(w<+d1))
| H5 => (lh1<*d1)
| W1 n l => Lmp l <* (d1^^n<+(w<+d1^^2))
| W2 n l => Lmp l <* (d1^^n<+(w^^2<+d1^^3))
end.

Inductive LBigStep: LS->LS->nat->nat->Prop :=
| LBigStep_H1:
    LBigStep H1 H1 1 1
| LBigStep_H2:
    LBigStep H2 H4 2 2
| LBigStep_H4:
    LBigStep H4 H5 1 1
| LBigStep_H5:
    LBigStep H5 H1 1 2
| LBigStep_W1_H1:
    LBigStep (W1 0 H1) H5 1 2
| LBigStep_W2_H1_0:
    LBigStep (W2 0 H1) H3 1 3
| LBigStep_W2_H1_1:
    LBigStep (W2 1 H1) H2 1 3
| LBigStep_W1 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+2 ->
    LBigStep (W1 k0 x) (W1 k1 x') (((n+1)*2^k1-1-1)*4+5) 2
| LBigStep_W2 x x' n k k0 k1:
    LBigStep x x' n k ->
    k0+k = k1+3 ->
    LBigStep (W2 k0 x) (W2 k1 x') (((n+1)*2^k1-1-1)*8+5) 3
.

Lemma LBigStep_n [x x' n k]:
  LBigStep x x' n k ->
  n >= 1.
Proof.
  intros H.
  induction H; lia.
Qed.

Inductive Lprefix: LS->nat->LS->Prop :=
| Lprefix_O x n: Lprefix x n x
| Lprefix_S1 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W1 k0 x')
| Lprefix_S2 x n x' k0:
  Lprefix x n x' ->
  k0>=n ->
  Lprefix x n (W2 k0 x')
.

Lemma Lprefix_halt [c x]:
  Lprefix H3 c x ->
  forall l, halts tm (l {{{ (hR,R) }}} Lmp x).
Proof.
  intros H.
  remember H3 as v1.
  gen Heqv1.
  induction H; intros; subst; cbn.
  - eapply halts_evstep.
    2: repeat step1; finish.
    eapply halted_halts.
    constructor.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
  - eapply halts_evstep.
    1: apply IHLprefix; trivial.
    es.
Qed.

Inductive LBigStep': LS->LS->Prop :=
| LBigStep'_intro x x' n k:
  LBigStep x x' n k ->
  LBigStep' x x'.

Lemma Lprefix_spec [x c x0 x']:
  Lprefix x (3+c) x0 ->
  LBigStep' x x' ->
  exists x0', Lprefix x' c x0' /\ LBigStep' x0 x0'.
Proof.
  intros H.
  remember (3+c) as v1.
  gen x' c.
  induction H; intros; subst.
  - eexists; split.
    2: apply H.
    constructor.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W1 with (k1:=k0+k-2).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
  - epose proof (IHLprefix _ _ eq_refl H6) as [x0' [I1 I2]].
    inverts I2.
    eexists; split.
    2: {
      econstructor.
      eapply LBigStep_W2 with (k1:=k0+k-3).
      1: eassumption.
      lia.
    }
    econstructor.
    1: eassumption.
    lia.
Qed.



Lemma LBigStep_spec [x x' n k]:
  LBigStep x x' n k ->
  exists l,
  sideRLs tm [(hR,(C,[]))] (Lmp x) (l<*(w'<+d0')^^k) /\
  sideRLs tm (hRL^^n) (l<*w') (Lmp x').
Proof.
  intros H.
  induction H.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - eexists; split.
    + solve_sideRLs.
    + solve_sideRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0<+d0'<+w<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
  - epose proof (LBigStep_n H) as Hn.
    destruct IHLBigStep as [l [I1 I2]].
    cbn[Lmp].
    eexists (_<*(d0'++w')^^k0<*w^^2); split.
    + do 2 rewrite <-Str_app_assoc.
      eapply segRLs_sideRLs_concat.
      2: apply I1.
      solve_segRLs.
    + rewrite lpow_add',H0,<-lpow_add'.
      do 2 rewrite <-Str_app_assoc.
      rewrite <-(app_nil_l (hRL^^_)).
      eapply @sideRLs_trans with (r2:=(l<*w'<*(d0^^k1<+(d0^^2<+d0'<+w^^2<+w')))).
      1: simpl_rotate; solve_sideRLs.
      eapply segRLs_sideRLs_concat.
      2: apply I2.
      eapply segRLs_concat.
      2: eapply D_IncsOvs.
      eapply segRLs_addmul'.
      1: epose proof (Nat.pow_nonzero 2 k1); lia.
      1: solve_segRLs.
      1: solve_segRLs.
Qed.

Definition RC n := w'^^(1+n) *> 0inf.

Lemma RC_Incs n m:
  sideRLs tm' (hLR^^n) (RC m) (RC (n+m)).
Proof.
  unfold RC.
  induction n.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  simpl_tape.
  solve_sideRLs.
Qed.

Lemma RC_Inc m r:
  RC m {{{ (hL,L) }}} r -->*
  RC (m+1) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.
  

Lemma mul_nz a b:
  a<>O ->
  b<>O ->
  a*b<>O.
Proof. lia. Qed.

Definition S1 a b x :=
  RC a {{{ (hR,R) }}} d1^^b *> Lmp x.

Lemma BigStep2 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (2+m2*3) (3+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*4+2)*2^(m2+1)-1+1+1) m2 (W2 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> ((d0^^2)<+w'^^2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0^^2<+w'^^2) (w2:=w^^2<+d1^^2).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=4) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep1 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (1+m2*3) (2+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1-1)*2+2)*2^(m2+1)-1+1+1) m2 (W1 (m1+k) x').
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> (d0<+w') *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I4:_). {
    eapply @segRLs_sideRLs_concat with (w1:=d0<+w') (w2:=w<+d1).
    2: eapply I3.
    eapply segRLs_addmul' with (a:=2) (b:=2) (c:=1%nat).
    1: epose proof (Nat.pow_nonzero 2 (m1+k)); lia.
    1: solve_segRLs.
    1: solve_segRLs.
  }
  clear I3.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I4.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I4.
  rewrite <-lrcons_lpow1 in I5.
  2: epose proof (Nat.pow_nonzero 2 (1+m2)); eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma BigStep0 [x x' n k m1 m2]:
  LBigStep x x' n k ->
  S1 (0+m2*3) (1+m1) x -->*
  S1 ((((n+1)*2^(m1+k)-1))*2^(m2+1)-1+1+1) (1+m2+m1+k) x'.
Proof.
  rewrite (Nat.add_comm m2 1).
  unfold S1.
  intros H.
  match goal with
  | |- _ -->* ?a => remember a as v1
  end.
  epose proof (LBigStep_n H) as Hn.
  epose proof (LBigStep_spec H) as [l [I1 I2]].
  inverts I1.
  inverts H11.
  unfold sideRL in H10.
  unfold to_DH_config in *.
  es; er.
  follow100 H10.
  mid (
  RC 1 {{{ (hR,R) }}} d1^^(1+m2) *> d0^^(m1+k) *> w'*>l).
  1: es.
  eassert (I3:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I2.
    eapply D_IncsOvs with (m:=(m1+k)).
  }
  clear I2.
  eassert (I5:_). {
    eapply segRLs_sideRLs_concat.
    2: eapply I3.
    eapply D_Ovs with (m:=(1+m2)).
  }
  clear I3.
  rewrite <-lrcons_lpow1 in I5.
  2:
    epose proof (Nat.pow_nonzero 2 (m1+k));
    epose proof (Nat.pow_nonzero 2 (1+m2));
    eapply mul_nz; try lia.
  epose proof (sideRLs_concat (RC_Incs _ 1) I5) as I6.
  follow100 I6.
  follow RC_Inc.
  subst.
  es.
Qed.

Lemma init:
  c0 -->*
  S1 57 5 H1.
Proof.
  unfold S1; cbn.
  solve_init.
Qed.

Inductive P: LS->nat->nat->nat->LS->Prop :=
| P_intro x c a b x0:
  a>=c*3 ->
  b>=c ->
  Lprefix x c x0 ->
  c0 -->* S1 a b x0 ->
  P x c a b x0
.

Lemma P_spec [x c a b x0 x']:
  P x (3+c) a b x0 ->
  LBigStep' x x' ->
  exists a' b' x0',
  P x' c a' b' x0'.
Proof.
  intros HP HL.
  inverts HP.
  divmod3 a.
  - replace b with (1+(b-1)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep0.
    3,4: eassumption.
    2: lia.
    match goal with
    | |- ?a*_-1+1+1 >= _ => remember a as v1
    end.
    assert (v1>=2). {
      subst v1.
      replace (b-1+k) with (2+(b-3+k)) by lia.
      epose proof (Nat.pow_nonzero 2 (b-3+k)).
      cbn; lia.
    }
    replace v1 with (v1-2+2) by lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v2
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (2+(b-2)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep1.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
  - replace b with (3+(b-3)) in * by lia.
    epose proof (Lprefix_spec H6 HL) as [x0' [I1 I2]].
    inverts I2.
    eexists _,_,_.
    econstructor.
    4: follow H7.
    4: apply BigStep2.
    4: eassumption.
    3: constructor; try assumption; lia.
    2: lia.
    rewrite Nat.mul_add_distr_r.
    match goal with
    | |- ?a+_-1+1+1 >= _ => remember a as v1
    end.
    epose proof (pow2_gt a0).
    rewrite Nat.pow_add_r.
    cbn; lia.
Qed.

Lemma P_W2_halt c a b x0:
  P (W2 (c*2) H1) (3+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b x0.
  induction c; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
    }
    destruct HP as [a' [b' [x0' HP]]].
    inverts HP.
    eapply halts_evstep.
    2: {
      follow H8.
      unfold S1.
      unfold to_DH_config; cbn.
      sr.
      finish.
    }
    apply (Lprefix_halt H7).
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      replace (S c*2+1) with (c*2+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc,HP.
Qed.
 
Lemma P_W1_halt c c1 a b x0:
  P (W2 (c1+2+c*2) (W1 c1 H1)) (c1*3+9+c*3) a b x0 ->
  halts tm c0.
Proof.
  gen a b c x0.
  induction c1; intros.
  - cbn in H.
    eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      do 2 econstructor.
      1: econstructor.
      replace (S(S(c*2))+2) with (c*2+1+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eassert _ as HP'. {
      eapply P_spec.
      1: apply HP.
      do 2 econstructor.
      1: econstructor.
      rewrite <-Nat.add_assoc.
      reflexivity.
    }
    destruct HP' as [a'0 [b'0 [x0'0 HP'0]]].
    eapply P_W2_halt,HP'0.
  - eassert _ as HP. {
      eapply P_spec.
      1: apply H.
      econstructor.
      econstructor.
      1: econstructor.
      1: econstructor.
      1: replace (S c1+1) with (c1+2) by lia; reflexivity.
      replace (S c1+2+c*2+2) with ((c1+2+c*2)+3) by lia.
      reflexivity.
    }
    destruct HP as [a' [b' [x0' HP]]].
    eapply IHc1,HP.
Qed.

Ltac R_mod :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  eassert (X:_) by (eapply (div_mod' a 3 _); rw_mod_1);
  rewrite X in *;
  clear X
end.

Ltac R_sub d :=
match goal with
| |- S1 ?a ?b ?c -->* _ =>
  replace b with (d+(b-d)) by (symmetry; apply sub_add'; shelve)
end.

Lemma halt: halts tm c0.
Proof.
  eapply P_W1_halt with (c1:=23) (c:=N.to_nat 11010035).
  econstructor.
  4:{
  follow init.
  change 57 with (0+19*3).
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep0 HL) as HB.
  follow HB.
  clear HB HL.
  change (1+1) with 2.
  change (4+1) with 5.
  change (1+19) with 20.
  change (20+4+1) with 25.
  R_mod.
  eassert (LBigStep H1 _ _ _) as HL by constructor.
  epose proof (BigStep1 HL) as HB.
  follow HB.
  clear HB HL.
  R_mod.
  R_sub 3.
  eassert (LBigStep (W1 (23+1) H1) _ _ _) as HL. {
    eapply LBigStep_W1 with (k1:=23).
    1: constructor.
    trivial.
  }
  epose proof (BigStep2 HL) as HB.
  follow HB.
  clear HB HL.
  change (2*2^5-1) with 63.
  finish.
  }
  3: {
    match goal with
    | |- Lprefix (W2 ?a _) _ (W2 ?b _) =>
        replace a with b by solve_nat_eq_by_N
    end.
    apply Lprefix_O.
  }
  1,2: replace (23*3+9+N.to_nat 11010035*3) with (N.to_nat 33030183) by solve_nat_eq_by_N.
  2: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  1: {
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply gt_ge_trans.
    1: apply pow2_gt.
    repeat solve_ge'.
    eapply mul1_ge.
    1: solve_ge.
    eapply ge_trans.
    1: apply pow2_ge32.
    1: solve_nat_ge_by_N.
    solve_nat_ge_by_N.
  }
  Unshelve.
  all: solve_ge.
Qed.

End TM7.


