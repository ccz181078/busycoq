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


