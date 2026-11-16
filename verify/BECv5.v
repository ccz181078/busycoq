From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.

Open Scope list.

Ltac flia := repeat (lia||f_equal).

Lemma highbit x:
  x<>O ->
  exists i, 2^i<=x<2^i*2.
Proof.
  induction x using lt_wf_ind; intros.
  divmod2_cases x.
  - unshelve epose proof (H n' _ _) as [i Hi].
    1,2: lia.
    eexists (S i).
    cbn; lia.
  - destruct (Nat.eqb_spec n' 0).
    1: exists O; lia.
    unshelve epose proof (H n' _ _) as [i Hi].
    1,2: lia.
    eexists (S i).
    cbn; lia.
Qed.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition LC0 n := BinInc <[0;1] n.
Definition R n m := [1] *> [1;0]^^(1+n) *> [0] *> [1;0]^^(m) *> const 0.

Notation hL := (A,[]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[]) (qR:=[]); es.
  er.
Qed.

Lemma LIncs n:
  sideRLs tm' (hLR^^n) (LC0 0) (LC0 n).
Proof.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    lowbitS_cases n.
    rewrite Nat.sub_add by lia.
    unfold LC0.
    rw_Bin.
    esx.
Qed.

Lemma LIncs' n:
  sideRLs tm' (hLR^^(n*2)) (LC0 n <* [0]) (LC0 0).
Proof.
  unfold LC0.
  induction n using lt_wf_ind.
  divmod2_cases n.
  - destruct (Nat.eqb_spec n' 0).
    + subst.
      esx.
    + unshelve epose proof (H n' _) as H.
      1: lia.
      rw_Bin.
      replace 0inf with ([0;0]*>0inf) by solve_const0_eq.
      eapply @segRLs_sideRLs_concat with (w1:=[0;0]).
      2: apply H.
      replace (n'*2*2) with (n'*2*2+0) by lia.
      apply segRLs_addmul''; esx.
  - unshelve epose proof (H n' _) as H.
    1: lia.
    rw_Bin.
    replace 0inf with ([0;0]*>0inf) by solve_const0_eq.
    eapply @segRLs_sideRLs_concat with (w1:=[0;1]).
    2: apply H.
    replace ((n'*2+1)*2) with (n'*2*2+2) by lia.
    apply segRLs_addmul''; esx.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (R n m) (R 0 (n+m)).
Proof.
  gen m.
  induction n; intros.
  - esx.
  - replace (S n) with (1+n) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: applys_eq (IHn (1+m)); flia.
    esx.
Qed.

Lemma ROv k i m:
  LC0 ((k*2+1)*2^i-1) <| R 0 m -->+
  LC0 k <* [0] <| R (1+i+m) 0.
Proof.
  unfold LC0,R.
  rw_Bin.
  es.
Qed.

Definition S '(a,b) := LC0 a <| R 0 b.

Lemma BigStep k i m:
  k*2<=(1+i+m) ->
  S ((k*2+1)*2^i-1,m) -->+
  S (1+i+m-k*2,1+i+m).
Proof.
  unfold S.
  intros.
  follow10 ROv.
  replace (1+i+m) with (k*2+(1+i+m-k*2)) by lia.
  epose proof (sideRLs_concat_1L (RIncs _ 0)) as I1.
  follow I1.
  - rewrite lpow_add.
    eapply sideRLs_trans.
    + apply LIncs'.
    + apply LIncs.
  - unfold to_DH_config.
    finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (6,6)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a<=1+b).
  2: lia.
  intros [a b] HP.
  lowbitS_cases a.
  eexists (_,_).
  split.
  - apply BigStep.
    zify_le_mul_r; lia.
  - lia.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LA---_1LA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition LC0 n := BinInc <[0;1] n.
Definition R n m := [1] *> [1;0]^^(1+n) *> [0] *> [1;0]^^(m) *> const 0.

Notation hL := (A,[]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Lemma LInc0 r n:
  LC0 n <| r -->*
  LC0 (1+n) |> r.
Proof.
  unfold LC0.
  er.
  eapply evstep_trans.
  1: apply progress_evstep.
  1: apply LBinInc_spec with (qL:=[]) (qR:=[]); es.
  er.
Qed.

Lemma LIncs n m:
  sideRLs tm' (hLR^^n) (LC0 m) (LC0 (n+m)).
Proof.
  induction n.
  - esx.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn.
    remember (n+m) as v1.
    replace (n+1+m) with (v1+1) by lia.
    lowbitS_cases v1.
    rewrite Nat.sub_add by lia.
    unfold LC0.
    rw_Bin.
    esx.
Qed.

Lemma LIncs' i n:
  2^i<=n<2^i*2 ->
  sideRLs tm' (hLR^^(2^i*2-1)) (LC0 n <* [1]) (LC0 (2^i*2)).
Proof.
  unfold LC0.
  gen n.
  induction i; intros.
  - replace n with 1%nat by lia.
    cbn.
    simpl_tape.
    esx.
  - rewrite Nat.pow_succ_r in * by lia.
    divmod2_cases n.
    + unshelve epose proof (IHi n' _) as IHi.
      1: lia.
      do 2 rewrite BinInc_mul2.
      replace (2*2^i*2-1) with (1+((2^i*2-1)*2+0)) by lia.
      rewrite lpow_add.
      eapply sideRLs_trans.
      1: esx.
      eapply @segRLs_sideRLs_concat with (w1:=[0;0]) (w2:=[0;0]).
      2: applys_eq IHi; flia.
      eapply segRLs_addmul''; esx.
    + unshelve epose proof (IHi n' _) as IHi.
      1: lia.
      rewrite BinInc_mul2.
      rewrite BinInc_mul2add1.
      replace (2*2^i*2-1) with (1+((2^i*2-1)*2+0)) by lia.
      rewrite lpow_add.
      eapply sideRLs_trans.
      1: esx.
      eapply @segRLs_sideRLs_concat with (w1:=[0;0]) (w2:=[0;0]).
      2: applys_eq IHi; flia.
      eapply segRLs_addmul''; esx.
Qed.

Lemma RIncs n m:
  sideRLs tm (hRL^^n) (R n m) (R 0 (n+m)).
Proof.
  gen m.
  induction n; intros.
  - esx.
  - replace (S n) with (1+n) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: applys_eq (IHn (1+m)); flia.
    esx.
Qed.

Lemma ROv k i m:
  LC0 ((k*2+1)*2^i-1) <| R 0 m -->+
  LC0 k <* [1] <| R (i+m) 1.
Proof.
  unfold LC0,R.
  rw_Bin.
  es.
Qed.

Definition S '(a,b) := LC0 a <| R 0 b.

Lemma BigStep k i0 i m:
  2^i0<=k<2^i0*2 ->
  2^i0*2-1<=i+m ->
  S ((k*2+1)*2^i-1,m) -->+
  S (1+i+m,1+i+m).
Proof.
  unfold S.
  intros.
  follow10 ROv.
  replace (i+m) with ((2^i0*2-1)+(i+m-(2^i0*2-1))) by lia.
  epose proof (sideRLs_concat_1L (RIncs _ 1)) as I1.
  follow I1.
  - rewrite lpow_add.
    eapply sideRLs_trans.
    + apply LIncs',H.
    + apply LIncs.
  - unfold to_DH_config.
    finish.
Qed.

Lemma BigStep_0 i m:
  S ((0*2+1)*2^i-1,m) -->+
  S (1+i+m,1+i+m).
Proof.
  unfold S.
  intros.
  follow10 ROv.
  replace ([1] *> LC0 0) with (LC0 1) by (cbn; solve_const0_eq).
  epose proof (sideRLs_concat_1L (RIncs _ 1)) as I1.
  follow I1.
  - apply LIncs.
  - unfold to_DH_config.
    finish.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S (6,6)).
  1: unfold S; esx.
  eapply progress_nonhalt_cond with (P:=fun '(a,b) => a=b).
  2: lia.
  intros [a b] HP.
  lowbitS_cases a.
  destruct (Nat.eqb_spec x 0) as [E|E].
  - subst.
    eexists (_,_). split.
    1: apply BigStep_0.
    lia.
  - epose proof (highbit x E) as [i0 Hi0].
    eexists (_,_). split.
    + eapply BigStep with (i0:=i0).
      1: lia.
      zify_le_mul_r; lia.
    + lia.
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RC_1RA0LD_0LC1LB_---0RF_1RF0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition tm' := flip tm.

Notation "l <| r" := (l <{{B}} [1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1] {{B}}> r) (at level 30).

Notation hL := (B,[1;0;0]).
Notation hR := (B,[1;1;1]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition LC a b := 0inf <* [1]^^a <* <[1;0;0] <* [1]^^b <* <[1;0].

Lemma LInc a b r:
  LC a (1+b) <| r -->*
  LC (1+a) b |> r.
Proof.
  unfold LC.
  es.
Qed.

Lemma LIncs a b:
  sideRLs tm' (hLR^^b) (LC a b) (LC (b+a) 0).
Proof.
  unfold LC.
  gen a.
  induction b; intros.
  - esx.
  - replace (S b) with (1+b) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    2: applys_eq (IHb (1+a)); flia.
    esx.
Qed.

Lemma LOv a r:
  LC a 0 <| r -->*
  LC 1 a |> [0] *> r.
Proof.
  unfold LC.
  es.
Qed.

Definition RC0 len n r := BinDec [0;0;0] [1;0;0] len n r.

Lemma RInc0 len n l r:
  1+n<2^len ->
  l |> RC0 len (1+n) r -->+
  l <| RC0 len n r.
Proof.
  eapply RBinDec_spec.
  es.
Qed.

Definition RC1 len n r := BinDec [0;1;0] [0;0;0] len n r.

Lemma RC0_0 len n r:
  n<2^len ->
  [0] *> RC0 len n r =
  RC1 len (2^len-1-n) ([0]*>r).
Proof.
  unfold RC0,RC1.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    reflexivity.
  - cbn[Nat.pow] in *.
    rewrite <-Nat.add_1_r.
    divmod2_cases n.
    1: replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
    2: replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
    1,2: rw_Bin; solve_pow2_lt;
    rewrite <-IHlen by lia; reflexivity.
Qed.

Lemma RIncs1 len n r:
  n<2^len ->
  sideRLs tm (hRL^^(n*2)) (RC1 len n r) ([0;0;0]^^len *> r).
Proof.
  unfold RC1.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
  - cbn[Nat.pow] in *.
    cbn[lpow]; rewrite Str_app_assoc.
    rewrite <-(Nat.add_1_r len).
    divmod2_cases n;
    rw_Bin; solve_pow2_lt.
    + eapply segRLs_sideRLs_concat.
      2: apply IHlen; lia.
      replace ((n'*2)*2) with (n'*2*2+0) by lia.
      eapply segRLs_addmul''; esx.
    + eapply segRLs_sideRLs_concat.
      2: apply IHlen; lia.
      replace ((n'*2+1)*2) with (n'*2*2+2) by lia.
      eapply segRLs_addmul''; esx.
Qed.

Lemma RIncs0 len n n0 r r':
  n<2^len ->
  sideRLs tm (hRL^^n0) r r' ->
  sideRLs tm (hRL^^(n0*2^len+n)) ([0;0;0]^^len*>r) (RC0 len (2^len-1-n) r').
Proof.
  unfold RC0.
  intros.
  gen n.
  induction len; intros.
  - applys_eq H0; flia.
  - cbn[Nat.pow] in *.
    cbn[lpow]; rewrite Str_app_assoc.
    rewrite <-(Nat.add_1_r len).
    divmod2_cases n.
    + replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: apply IHlen; lia.
      replace (n0*2*2^len+n'*2) with ((n0*2^len+n')*2+0) by lia.
      apply segRLs_addmul''; esx.
    + replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: apply IHlen; lia.
      replace (n0*2*2^len+(n'*2+1)) with ((n0*2^len+n')*2+1) by lia.
      apply segRLs_addmul''; esx.
Qed.

Lemma RIncs len n n0 n1 r r':
  n<2^len ->
  n1<2^len ->
  sideRLs tm (hRL^^n0) ([0]*>r) r' ->
  sideRLs tm (hRL^^(n*2+(n0*2^len+n1))) ([0]*>RC0 len (2^len-1-n) r) (RC0 len (2^len-1-n1) r').
Proof.
  intros.
  rewrite RC0_0 by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs1 len n); flia.
  apply RIncs0; assumption.
Qed.

Definition S0 a len n r :=
  LC a 0 <| RC0 len (2^len-1-n) r.

Lemma OvIncs' len n n0 n1 r r':
  n<2^len ->
  n1<2^len ->
  (n*2+(n0*2^len+n1)) <> O ->
  sideRLs tm (hRL^^n0) ([0]*>r) r' ->
  S0 (n*2+(n0*2^len+n1)-1) len n r -->+
  S0 (n*2+(n0*2^len+n1)) len n1 r'.
Proof.
  intros.
  unfold S0.
  follow LOv.
  epose proof (sideRLs_concat) as I.
  rewrite (lrcons_lpow1 hR hL (n*2+(n0*2^len+n1))) in I by lia.
  specialize (I (LIncs 1 _) (RIncs _ _ _ _ _ _ H H0 H2)).
  unfold to_DH_config in I.
  follow10 I.
  finish.
Qed.

Lemma OvIncs len n n0 n1 r r':
  n<2^len ->
  n1<2^len ->
  (n*2+(n0*2^len+n1)) <> O ->
  sideRLs tm (hRL^^n0) ([0]*>r) r' ->
  S0 (n*2+(n0*2^len+n1)-1) len n r -->*
  S0 (n*2+(n0*2^len+n1)) len n1 r'.
Proof.
  intros.
  apply progress_evstep,OvIncs'; assumption.
Qed.

Lemma OvIncs_a len n n1 r:
  n*2+1<n1 ->
  n1<2^len ->
  n*3+2^len*2+1=n1*3 ->
  S0 (n*2+(1*2^len+n1)-1) len n r -->*
  S0 ((S n)*2+(1*2^len+(S n1))-1) len (S n) ([1;0;1]*>r).
Proof.
  intros.
  follow OvIncs.
  1,2: lia.
  1: esx.
  remember (n*2+2^len+1-n1) as v1.
  mid (S0 (n1*2+(0*2^len+v1)-1) len n1 (1>>r)).
  1: finish.
  follow OvIncs.
  1,2: lia.
  1: esx.
  remember (n1*2+1-(2^len+v1)) as v2.
  mid (S0 (v1*2+(1*2^len+v2)-1) len v1 (0>>1>>r)).
  1: finish.
  follow OvIncs.
  1,2,3: lia.
  1: esx.
  finish.
Qed.

Lemma OvIncs_b len n n1 r:
  n*2+1<n1 ->
  n1<2^len ->
  n*3+2^len+1=n1*3 ->
  S0 (n*2+(1*2^len+n1)-1) len n r -->*
  S0 ((S n)*2+(1*2^len+(S n1))-1) len (S n) ([0;0;1]*>r).
Proof.
  intros.
  follow OvIncs.
  1,2: lia.
  1: esx.
  remember (n*2+2^len+1-n1) as v1.
  mid (S0 (n1*2+(0*2^len+v1)-1) len n1 (1>>r)).
  1: finish.
  follow OvIncs.
  1,2: lia.
  1: esx.
  remember (n1*2+1-(v1)) as v2.
  mid (S0 (v1*2+(0*2^len+v2)-1) len v1 (0>>1>>r)).
  1: finish.
  follow OvIncs.
  1,2,3: lia.
  1: esx.
  finish.
Qed.

Lemma OvIncs_b' len n n1 r:
  n1<=n*2+1 ->
  n<2^len ->
  n1<2^len ->
  n*3+2^len+1=n1*3 ->
  S0 (n*2+(1*2^len+n1)-1) len n r -->*
  S0 ((S n)*2+(1*2^len+(S n1))-1) len (S n) ([0;0;1]*>r).
Proof.
  intros.
  follow OvIncs.
  1: lia.
  1: esx.
  remember (n*2+1-n1) as v1.
  mid (S0 (n1*2+(1*2^len+v1)-1) len n1 (1>>r)).
  1: finish.
  follow OvIncs.
  1,2: lia.
  1: esx.
  remember (n1*2+1-(2^len+v1)) as v2.
  mid (S0 (v1*2+(2*2^len+v2)-1) len v1 (1>>1>>r)).
  1: finish.
  follow OvIncs.
  1-3: lia.
  1: esx.
  finish.
Qed.

Lemma OvIncs_b'' len n n1 r:
  n<2^len ->
  n1<2^len ->
  n*3+2^len+1=n1*3 ->
  S0 (n*2+(1*2^len+n1)-1) len n r -->*
  S0 ((S n)*2+(1*2^len+(S n1))-1) len (S n) ([0;0;1]*>r).
Proof.
  intros.
  destruct (Nat.ltb_spec (n*2+1) n1).
  - apply OvIncs_b; lia.
  - apply OvIncs_b'; lia.
Qed.

Lemma pow4_mod3 i:
  2^(i*2) mod 3 = 1%nat.
Proof.
  induction i; cbn - [Nat.modulo]; lia.
Qed.

Lemma OvIncss_a len n n1 r:
  n1*3 = (2^(len)*2+1) ->
  n+1<=n1 ->
  n+n1<=2^len ->
  S0 ((1*2^(len)+n1)-1) (len) 0 r -->*
  S0 (n*3+(1*2^(len)+n1)-1) (len) n ([1;0;1]^^n*>r).
Proof.
  intros.
  induction n.
  - finish.
  - follow IHn.
    1,2: lia.
    follow (OvIncs_a len n (n+n1) ([1;0;1]^^n*>r)).
    1-2: lia.
    finish.
Qed.

Lemma S0_000 a len r:
  S0 a len 0 (0>>0>>0>>r) =
  S0 a (len+1) 0 r.
Proof.
  unfold S0.
  do 3 f_equal.
  do 2 rewrite Nat.sub_0_r.
  unfold RC0.
  rw_Bin; solve_pow2_lt.
  st; trivial.
Qed.

Lemma OvIncss_b len n n1 r:
  n1*3 = 2^len+1 ->
  n+n1<=2^len ->
  S0 ((1*2^len+n1)-1) len 0 r -->*
  S0 (n*3+(1*2^len+n1)-1) len (n) ([0;0;1]^^n*>r).
Proof.
  intros.
  induction n.
  - finish.
  - follow IHn.
    1: lia.
    follow (OvIncs_b'' len n (n+n1) ([0;0;1]^^n*>r)).
    1-2: lia.
    finish.
Qed.

Definition S' '(i,r) :=
  S0 (2^(i*2)*80/3) (i*2+4) 0 r.

Lemma init:
  c0 -->*
  S' (O,[0]^^14*>[1;0;0;1]*>0inf).
Proof.
  unfold S',S0.
  esx.
Qed.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Ltac OvIncs :=
  follow OvIncs;
  [ rw_pa; lia
  | rw_pa; lia
  | rw_pa; lia
  | esx
  | ].

Local Opaque Nat.div Nat.modulo.

Lemma BigStep i r:
  exists r',
  S' (i,r) -->+
  S' (S i,r').
Proof.
  remember (2^(i*2)*2^4) as w.
  epose proof (OvIncss_a (i*2+4) ((w-1)/3) ((w*2+1)/3) _) as I.
  epose proof (pow4_mod3 i).
  epose proof (OvIncss_b (i*2+5) ((w*4-1)/3) ((w*2+1)/3) _) as I'.
  eexists.
  unfold S'.
  rw_pa.
  follow I.
  1-3: lia.
  clear I.
  replace ((w-1)/3) with (S((w-4)/3)) by lia.
  cbn[lpow]; rewrite Str_app_assoc.
  remember ([1;0;1]^^((w-4)/3)*>r) as r0.
  mid01 (S0 ((w-1)/3*2+(2*2^(i*2+4)+0)-1) (i * 2 + 4) ((w - 1) / 3) (1 >> 0 >> 1 >> r0)).
  1: rw_pa; finish.
  OvIncs.
  mid01 (S0 ((w*8-2) / 3) (i * 2 + 4) 0 (0 >> 0 >> 0 >> 1 >> r0)).
  1: rw_pa; finish.
  rewrite S0_000.
  rw_pa.
  subst r0.
  follow I'.
  1-2: lia.
  clear I'.
  replace (2^(S i*2)*80/3) with ((w*20-2)/3) by (cbn - [Nat.div]; rw_pa; lia).
  remember ([1;0;1]^^((w-4)/3)*>r) as r0.
  remember ([0;0;1]^^((w*4-1)/3)*>1>>r0) as r1.
  mid01 (S0 ((w * 4 - 1)/3*2 + (2 * (2 ^ (i*2+5)) + 0) - 1) (i * 2 + 5) ((w * 4 - 1) / 3) r1).
  1: rw_pa; finish.
  subst r0 r1.
  eapply progress_evstep_trans.
  1: apply OvIncs'.
  1-3: rw_pa; lia.
  1: esx.
  replace ((w*4-1)/3) with (S((w*4-4)/3)) by lia.
  cbn.
  rewrite S0_000.
  rw_pa.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros [i r].
  destruct (BigStep i r) as [x I].
  eexists (_,_).
  apply I.
Qed.

End TM3.


