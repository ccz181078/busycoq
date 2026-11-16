From BusyCoq Require Import Individual62.
From BusyCoq Require Import Longitudinal.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Ltac es :=
  simpl_rotate;
  repeat intro;
  unfold to_DH_config; cbn;
  execute_with_shift_rule.

Ltac side_S :=
  eapply sideRLseq_S; [es|].

Ltac side_Ss :=
  (repeat side_S);
  simpl_rotate;
  try apply sideRLseq_O.

Ltac ee :=
  es; er; finish;
  repeat f_equal;
  repeat rewrite Str_cons_def;
  repeat rewrite Str_app_assoc_1;
  cbn[app];
  reflexivity.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RC_0LA1RE_---0RF_0LA0RB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (F,[0]).
Definition hL':DH0 := (B,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA---_0RF1RE_0LA0RB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (F,[0]).
Definition hL':DH0 := (B,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RD_1LD1RE_0LA0RF_0RD1RE_0RC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (B,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC1RF_1LD1RE_0LA0RB_0RD1RE_0LA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (B,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM4.


Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC1RD_0RD1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (E,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM5.


Module TM6.

Definition tm := Eval compute in (TM_from_str "1LB1RA_0LC1RE_1RD0LD_0RA1RB_---0RF_0LC0RD").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (F,[0]).
Definition hL':DH0 := (D,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM6.


Module TM7.

Definition tm := Eval compute in (TM_from_str "1RB0LB_0RC0LB_1LD1RE_0LA0RF_0RD1RE_0RC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (B,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM7.


Module TM8.

Definition tm := Eval compute in (TM_from_str "1RB0LE_0RC---_1LD1RF_0LA0RB_0RC0LE_0RD1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[0]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (E,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM8.


Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC---_1RD0LD_0RA1RB_0RF1RE_0LC0RD").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (F,[0]).
Definition hL':DH0 := (D,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM9.


Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LD_0RA1RF_0RB1RE_0LC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (D,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM10.


Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RE_0RA1RB").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (F,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM11.


Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA1RB_0RB1RE_0RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (D,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM12.


Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RD_1RD0LF_0RA---_0RB1RE_0RA0LF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (F,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM13.


Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0RF_1RD0LD_0RA0LD_0RB1RE_0RA---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (A,[0]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (D,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ld1' := [1;0;1;0].
Definition ldh := const 0 <* [1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3); reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM14.


Module TM15.

Definition tm := Eval compute in (TM_from_str "1RB---_1LC0RF_1RD0LC_0LE0RA_1RA1LC_0RD1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[1]).
Definition hL:DH0 := (C,[0]).
Definition hR':DH0 := (D,[0]).
Definition hL':DH0 := (C,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ldh := const 0 <* <[1;0].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  unfold ld0,ld1,ldh.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [13])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM15.


Module TM16.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA0RD_1LA0LC_1RE1RD_1RB0RF_0RB---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (B,[]).
Definition hL:DH0 := (A,[]).
Definition hR':DH0 := (E,[]).
Definition hL':DH0 := (C,[]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ldh := const 0 <* <[1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  unfold ld0,ld1,ldh.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM16.


Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LA_1LB0RD_1RE1RD_1RC0RF_0RC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (B,[]).
Definition hR':DH0 := (E,[]).
Definition hL':DH0 := (A,[]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ldh := const 0 <* <[1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  unfold ld0,ld1,ldh.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[13],2,4)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [13])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM17.


Module TM18.

Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC0RF_1LD0RA_1RC0LE_1LD0LE_0RC---").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (C,[]).
Definition hL:DH0 := (D,[]).
Definition hR':DH0 := (B,[]).
Definition hL':DH0 := (E,[]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[0;1;0;0].
Definition ld1 := <[0;1;0;1].
Definition ldh := const 0 <* <[1].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  unfold ld0,ld1,ldh.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (5,[3],13,0)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply P1; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM18.


Module TM19.

Definition tm := Eval compute in (TM_from_str "1RB0LA_0LC0RD_1RD1LA_1RE---_1LA0RF_0RB1RF").
Definition tm' := flip tm.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition hR:DH0 := (E,[1]).
Definition hL:DH0 := (A,[0]).
Definition hR':DH0 := (B,[0]).
Definition hL':DH0 := (A,[0]).
Definition hRL := [(hR,hL)].
Definition hRL' := [(hR',hL')].

Definition ld0 := <[1;0;0;0].
Definition ld1 := <[1;0;1;0].
Definition ldh := const 0 <* <[1;0].

Definition w0 := [0;1;0].
Definition w1 := [1;1;0].
Definition w2 := [1;0;0].

Definition d0' := [0; 1;0;1;0; 1;0].
Definition d1' := [1;0;0; 1;0;1;0].

Lemma w0_Inc n:
  segRLs tm (hRL^^(2+n)) (hRL' ++ hRL^^n) w0 w2.
Proof.
  rewrite lpow_add.
  eapply segRLs_trans.
  2: {
    eapply segRLs_wall.
    1: ee.
    1: ee.
  }
  eapply segRLs_S.
  1: ee.
  eapply segRLs_S'.
  3: constructor.
  1: ee.
  1: ee.
Qed.

Lemma w0s_Inc n:
  segRLs tm (hRL^^(n*2)) (hRL'^^n) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  replace (S n*2) with (2+n*2) by lia.
  eapply segRLs_concat.
  1: apply w0_Inc.
  eapply segRLs_trans.
  2: apply IHn.
  change (hRL') with (hRL'^^1).
  eapply segRLs_wall.
  1: ee.
  1: ee.
Qed.

Lemma RD1_Inc k n:
  segRLs tm (hRL^^k) (hRL^^(k*2)) (w2^^n ++ d1') (w2^^n ++ d1').
Proof.
  eapply segRLs_concat.
  1: eapply segRLs_wall.
  1: ee.
  1: ee.
  eapply BCR.Incs.
  3: ee.
  unfold hL,hR.
  1: ee.
  1: ee.
Qed.

Lemma RD_Inc k n m:
  segRLs tm (hRL'^^k ++ hRL^^(n*2+2+m)) (hRL'^^(k*2+n*2+2) ++ hRL^^(m*2)) (w0^^n ++ d0') (w2^^n ++ d1').
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply segRLs_trans.
  1:{
    eapply segRLs_concat.
    1: eapply segRLs_wall.
    1: ee.
    1: ee.
    eapply BCR.Incs.
    3: ee.
    1: ee.
    1: ee.
  }
  eapply segRLs_concat.
  - eapply segRLs_trans.
    1: apply w0s_Inc.
    rewrite <-lpow_add.
    eapply segRLs_wall.
    1: ee.
    1: ee.
  - eapply segRLs_trans.
    1: {
      eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
    }
    rewrite lpow_add.
    eapply segRLs_trans.
    + eapply segRLs_S.
      1: ee.
      eapply segRLs_1_2.
      1: ee.
      1: ee.
      1: ee.
    + eapply BCR.Incs.
      3: ee.
      1: ee.
      1: ee.
Qed.

Definition RH0 a b c := w2^^a *> w0^^b *> [0] *> w0^^c *> const 0.
Lemma RH0_Inc' n b c:
  sideRLs tm (hRL'^^(n*2)) (RH0 0 b (1+c)) (RH0 0 (n+b) (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH0,w0.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc n b c:
  sideRLs tm (hRL^^(n*4)) (RH0 0 (n+b) (1+c)) (RH0 (n*2) b (1+c)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*4) with (n*4+4) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (S b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc'_O n b:
  sideRLs tm (hRL'^^n) (RH0 0 (b) (0)) (RH0 0 (n+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH0_Inc_O n b:
  sideRLs tm (hRL^^(n*2)) (RH0 0 (1+b) (0)) (RH0 (n) (1+b) (0)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (IHn (b)); f_equal; lia.
  unfold RH0,w0,w2.
  simpl_tape.
  side_Ss.
Qed.

Definition RH1 a b := w2^^a *> [0] *> w2^^b *> const 0.

Lemma RH0_Ov a c:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (2+c)) (w2^^a *> d1' *> RH1 1 (1+c)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
Qed.

Lemma RH0_Ov_O a:
  sideRLs tm (hRL^^2) (RH0 (1+a) 0 (1)) (w2^^a *> d1' *> RH1 2 (0)).
Proof.
  unfold RH0,RH1,d1',w0,w2.
  side_Ss.
  repeat rewrite <-const_unfold.
  constructor.
Qed.

Lemma RH1_Inc n a b:
  sideRLs tm (hRL^^(n*2)) (RH1 a (1+b)) (RH1 (n+a) (1+b)).
Proof.
  gen b.
  induction n; intros.
  1: constructor.
  replace (S n*2) with (n*2+2) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH1_Inc_O n a:
  sideRLs tm (hRL^^(n)) (RH1 a (0)) (RH1 (n+a) (0)).
Proof.
  induction n; intros.
  1: constructor.
  replace (S n) with (n+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply IHn.
  unfold RH1,w2.
  simpl_tape.
  side_Ss.
Qed.

Lemma RH_Incs_2 m n a b:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) (2+b)) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n+1) (1+b)).
Proof.
  remember (m*2+a*2+1) as v1.
  change (2+b) with (1+(1+b)).
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 (1+b)); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc.
Qed.

Lemma RH_Incs_1 m n a:
  sideRLs tm (hRL'^^(m*2) ++ hRL^^((m+(1+a))*4+2+n)) (RH0 0 (1+a) 1) ((w2^^(m*2+a*2+1)++d1') *> RH1 (n*2+2) 0).
Proof.
  remember (m*2+a*2+1) as v1.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'.
  eapply sideRLs_trans.
  1: applys_eq (RH0_Inc (m+(1+a)) 0 0); f_equal; lia.
  replace ((m+(1+a))*2) with (1+v1) by lia.
  eapply sideRLs_trans.
  1: apply RH0_Ov_O.
  rewrite <-Str_app_assoc.
  eapply segRLs_sideRLs_concat.
  1: apply RD1_Inc.
  eapply RH1_Inc_O.
Qed.

Lemma RH_Incs_0 m n a:
  sideRLs tm (hRL'^^m ++ hRL^^(n*2)) (RH0 0 (1+a) 0) (RH0 n (1+(m+a)) 0).
Proof.
  repeat rewrite lpow_add.
  repeat rewrite <-app_assoc.
  eapply sideRLs_trans.
  1: apply RH0_Inc'_O.
  replace (m+(1+a)) with (1+(m+a)) by lia.
  apply RH0_Inc_O.
Qed.

Fixpoint RC(w d:list Sym)(ls:list nat):list Sym :=
match ls with
| nil => nil
| n::ls0 => (RC w d ls0) ++ ((w^^n) ++ d)
end.

Lemma RC_rot ls r:
  RC w2 d1' ls *> [1;0] *> r =
  [1;0] *> RC w0 d0' ls *> r.
Proof.
  gen r.
  induction ls; intros r; cbn[RC].
  1: reflexivity.
  repeat rewrite Str_app_assoc.
  gen IHls.
  unfold w0,w2,d0',d1'; cbn.
  simpl_rotate.
  intros IHls.
  rewrite IHls.
  reflexivity.
Qed.

Lemma RH1_rot a b:
  RH1 (1+a) b =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RH0_rot a b:
  RH0 (1+a) b 0 =
  [1;0] *> RH0 0 a b.
Proof.
  unfold RH0,RH1,w0,w2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma R1_rot ls a b:
  RC w2 d1' ls *> RH1 (1+a) b =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH1_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Lemma R0_rot ls a b:
  RC w2 d1' ls *> RH0 (1+a) b 0 =
  [1;0] *> RC w0 d0' ls *> RH0 0 a b.
Proof.
  rewrite RH0_rot.
  rewrite RC_rot.
  reflexivity.
Qed.

Fixpoint Rn(n0:nat)(ls:list nat):Z :=
(match ls with
| nil => Z.of_nat n0
| n::ls0 => ((Rn n0 ls0) - (Z.of_nat n)*2 - 2)*2
end)%Z.

Fixpoint Rm(ls:list nat):nat :=
match ls with
| nil => 0
| n::ls0 => (Rm ls0)*2+n*2+2
end.

Lemma Rn_spec n0 ls:
  (0 <= (Rn n0 ls))%Z ->
  segRLs tm (hRL^^n0) (hRL'^^(Rm ls) ++ hRL^^(Z.to_nat (Rn n0 ls))) (RC w0 d0' ls) (RC w2 d1' ls).
Proof.
  induction ls.
  - intros H.
    cbn.
    rewrite Nat2Z.id.
    apply segRLs_nil.
  - cbn.
    intros H.
    eapply segRLs_concat.
    1: apply IHls; lia.
    applys_eq (RD_Inc (Rm ls) a (Z.to_nat (Rn n0 ls)-(a*2+2))).
    1,2: repeat (try lia; f_equal).
Qed.

Lemma LOv n r:
  ldh <* ld1^^n {{{ (hL,L) }}} [1;0] *> r -->+
  ldh <* ld0^^(S n) {{{ (hR,R) }}} r.
Proof.
  unfold ld0,ld1,ldh.
  es.
Qed.

Definition config '(k,ls,a,b) :=
  ldh <* ld0^^k {{{ (hR,R) }}} RC w0 d0' ls *> RH0 0 a b.

Lemma RC_def w d ls n r:
  RC w d ls *> (w^^n++d) *> r =
  RC w d (n::ls) *> r.
Proof.
  cbn.
  repeat rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma BigStep2 k m n ls a b:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),(2+b)) -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n, 1+b).
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_2.
  - rewrite RC_def.
    rewrite (Nat.add_comm n 1).
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep1 k m n ls a:
  Rm ls = m*2 ->
  Z.to_nat (Rn (2^k) ls) = (m+(1+a))*4+2+n ->
  config (k,ls,(1+a),1)%nat -[ tm ]->+
  config (S k, m*2+a*2+1::ls, n*2+1, 0)%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_1.
  - rewrite RC_def.
    replace (n*2+2) with (1+(n*2+1)) by lia.
    rewrite R1_rot.
    apply LOv.
Qed.

Lemma BigStep0 k m n ls a:
  Rm ls = m ->
  Z.to_nat (Rn (2^k) ls) = ((1+n)*2) ->
  config (k,ls,(1+a),0)%nat -[ tm ]->+
  config (S k, ls, n, 1+(m+a))%nat.
Proof.
  intros Hm Hn.
  eapply progress_trans.
  - unfold config.
    eapply sideRLs_concat.
    + eapply segRLs_sideRLs_concat.
      1: eapply (BC.Incs _ hL hR ld0 ld1).
      1: ee.
      1: ee.
      1: ee.
      constructor.
    + rewrite lrcons_lpow1.
      2: eapply Nat.pow_nonzero; lia.
      eapply segRLs_sideRLs_concat.
      1: apply Rn_spec.
      1: lia.
      rewrite Hm,Hn.
      apply RH_Incs_0.
  - rewrite R0_rot.
    apply LOv.
Qed.

Fixpoint Rx (ls:list nat) :=
(match ls with
| nil => 0
| n::ls0 => (Rx ls0)*2 + (n+1)
end)%nat.

Lemma Rm_def ls:
  Rm ls = Rx ls * 2.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn0_def ls:
  (Rn 0 ls = Z.of_nat (Rx ls) * -4)%Z.
Proof.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Lemma Rn_def n0 ls:
  (Rn n0 ls =
  Z.of_nat (Rx ls) * -4 + Z.of_nat (n0*2^(length ls)))%Z.
Proof.
  rewrite <-Rn0_def.
  induction ls.
  - cbn; lia.
  - gen IHls; cbn; lia.
Qed.

Inductive P: (nat*(list nat)*nat*nat)->Prop :=
| P2 k ls b:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,6,1+b)
| P1 k ls:
    2^(k+length ls) = (Rx ls)*8+32 ->
    P (k,ls,13,0)%nat
| P0 k ls:
    2^(k+length ls) = (Rx ls)*16+64 ->
    P (k, ls, Rx ls * 2 + 15, Rx ls * 2 + 13)
| P3 k ls b:
    2^(k+length ls) = (Rx ls)*8+16 ->
    P (k,ls,2,2+b)
.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=config (6,[25;1],2,8)%nat).
  1: cbn; solve_init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply (P3 6 [25;1])%nat; reflexivity.
  intros [[[k ls] a] b] HP.
  inverts HP.
  - destruct b0 as [|b0].
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep1 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P1.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
    + eexists (_,_,_,_).
      split.
      * eapply (BigStep2 k (Rx ls) 6).
        1: apply Rm_def.
        rewrite Rn_def.
        rewrite <-Nat.pow_add_r.
        lia.
      * eapply P2.
        cbn.
        rewrite <-Nat.add_succ_comm.
        cbn.
        lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep0) with (n:=Rx ls * 2 + 15).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + applys_eq (P0 (S k) ls).
      1: repeat (try lia; f_equal).
      cbn.
      lia.
  - eexists (_,_,_,_).
    split.
    + replace (Rx ls*2+13) with (2+(Rx ls*2+11)) by lia.
      replace (Rx ls*2+15) with (1+(Rx ls*2+14)) by lia.
      eapply (BigStep2) with (n:=2).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + replace (1+(Rx ls*2+11)) with (2+(Rx ls*2+10)) by lia.
      eapply P3.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
  - eexists (_,_,_,_).
    split.
    + eapply (BigStep2) with (n:=6).
      1: apply Rm_def.
      rewrite Rn_def.
      rewrite <-Nat.pow_add_r.
      lia.
    + eapply P2.
      cbn.
      rewrite <-Nat.add_succ_comm.
      cbn.
      rewrite H0.
      lia.
Qed.
End TM19.
