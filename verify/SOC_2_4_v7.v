From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import Longitudinal.
From BusyCoq Require Import BinaryCounter_v2.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_0RA0LC_1RE1LE_1RC0RF_---1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation rd0' := [0;1;1;0].
Notation rd1' := [0;0;1;0].
Notation rd0 := [0;0;1;1].
Notation rd1 := [0;0;0;1].

Notation hR := (D,[1]).
Notation hL := (C,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{C}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{D}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Lemma LOv len r:
  LC len 0 <| [0] *> r -->*
  LC (len+1) ((2^len-1)*2) |> r.
Proof.
  unfold LC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Definition RC len n := BinDec rd0 rd1 len n 0inf.
Definition RC' len n := BinDec rd0' rd1' len n 0inf.

Lemma RInc l len n:
  1+n<2^len ->
  l |> RC len (1+n) -->+
  l <| RC len n.
Proof.
  intros.
  eapply RBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RIncs len n:
  n<2^len ->
  sideRLs tm (hRL^^n) (RC len (2^len-1)) (RC len (2^len-1-n)).
Proof.
  induction n; intros.
  - applys_eq sideRLseq_O; flia.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn; lia.
    econstructor.
    2: constructor.
    intro.
    applys_eq (RInc l len (2^len-1-(n+1))).
    2: lia.
    unfold to_DH_config; flia.
Qed.

Lemma Rshift len n:
  n<2^len ->
  RC len n =
  [0] *> RC' len n.
Proof.
  unfold RC,RC'.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    cbn.
    solve_const0_eq.
  - cbn[Nat.pow] in *.
    replace (S len) with (len+1) by lia.
    divmod2_cases n;
    rw_Bin; solve_pow2_lt;
    rewrite IHlen by lia;
    reflexivity.
Qed.

Lemma RIncs' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' len (2^len-1-n)) (RC (1+len) (2^(1+len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma RIncs'' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' (1+len) (2^len-1-n)) (RC (len) (2^(len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
    es.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma ROv len:
  sideRLs tm hRL (RC len 0) (RC (len+1) (2^(len+1)-1)).
Proof.
  unfold RC.
  rw_Bin.
  esx.
Qed.

Lemma RIncsOv len:
  sideRLs tm (hRL^^(2^len)) (RC len (2^len-1)) (RC (len+1) (2^(len+1)-1)).
Proof.
  remember (2^len-1) as v1.
  replace (2^len) with (v1+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply ROv.
  subst.
  applys_eq (RIncs len (2^len-1)); flia.
Qed.

Definition S' '(lenL,lenR,n) := LC lenL 0 <| RC lenR (2^lenR-1-n).

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep lenL lenR n lenR' n':
  n<2^lenR ->
  sideRLs tm (hRL^^(2^lenL*2-1)) (RC' lenR (2^lenR-1-n)) (RC lenR' (2^lenR'-1-n')) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR',n').
Proof.
  unfold S'.
  intros.
  rewrite (Rshift lenR) by lia.
  follow LOv.
  epose proof (sideRLs_concat) as I1.
  erewrite lrcons_lpow1 in I1.
  2: shelve.
  epose proof (LIncs _ (2^lenL*2-1-1) _) as I2.
  specialize (I1 I2 H0).
  applys_eq I1;
  unfold to_DH_config; flia.
  Unshelve.
  all: rw_pa; lia.
Qed.

Lemma BigStep1 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+n0 ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite Nat.add_comm.
  apply RIncs; lia.
Qed.

Lemma BigStep2 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^(lenR+1)+n0) ->
  n0<2^(lenR+1+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite (Nat.add_comm 1 lenR).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma BigStep0 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^lenR+n0) ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR+1,2^lenR+n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: rw_pa; lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs'' lenR n); rw_pa; flia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma init:
  c0 -->*
  S' (4,4,14).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(lenL,lenR,n) => n<2^lenR /\ lenR<>O /\ (lenL=lenR \/ lenL=lenR+1)).
  2: lia.
  intros [[lenL lenR] n] [I1 [I2 I3]].
  remember (lenR-1) as lenR'.
  replace lenR with (lenR'+1) in * by lia.
  destruct I3 as [I3|I3]; subst lenL.
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1)*2-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1) lenR' (n-2^lenR') (2^lenR'*6-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep2 with (n0:=2^(lenR'+1+1)-1-(n*3+1)).
      all: rw_pa; lia. }
    destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)*2-1)) as [E0|E0].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1+1) lenR' (n-2^lenR') (2^lenR'*10-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC0RF_0RD0LC_1LE1RA_1LC0LB_---1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation rd0' := [0;1;1;0].
Notation rd1' := [0;0;1;0].
Notation rd0 := [0;0;1;1].
Notation rd1 := [0;0;0;1].

Notation hR := (A,[1]).
Notation hL := (C,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{C}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{A}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Lemma LOv len r:
  LC len 0 <| [0] *> r -->*
  LC (len+1) ((2^len-1)*2) |> r.
Proof.
  unfold LC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Definition RC len n := BinDec rd0 rd1 len n 0inf.
Definition RC' len n := BinDec rd0' rd1' len n 0inf.

Lemma RInc l len n:
  1+n<2^len ->
  l |> RC len (1+n) -->+
  l <| RC len n.
Proof.
  intros.
  eapply RBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RIncs len n:
  n<2^len ->
  sideRLs tm (hRL^^n) (RC len (2^len-1)) (RC len (2^len-1-n)).
Proof.
  induction n; intros.
  - applys_eq sideRLseq_O; flia.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn; lia.
    econstructor.
    2: constructor.
    intro.
    applys_eq (RInc l len (2^len-1-(n+1))).
    2: lia.
    unfold to_DH_config; flia.
Qed.

Lemma Rshift len n:
  n<2^len ->
  RC len n =
  [0] *> RC' len n.
Proof.
  unfold RC,RC'.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    cbn.
    solve_const0_eq.
  - cbn[Nat.pow] in *.
    replace (S len) with (len+1) by lia.
    divmod2_cases n;
    rw_Bin; solve_pow2_lt;
    rewrite IHlen by lia;
    reflexivity.
Qed.

Lemma RIncs' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' len (2^len-1-n)) (RC (1+len) (2^(1+len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma RIncs'' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' (1+len) (2^len-1-n)) (RC (len) (2^(len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
    es.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma ROv len:
  sideRLs tm hRL (RC len 0) (RC (len+1) (2^(len+1)-1)).
Proof.
  unfold RC.
  rw_Bin.
  esx.
Qed.

Lemma RIncsOv len:
  sideRLs tm (hRL^^(2^len)) (RC len (2^len-1)) (RC (len+1) (2^(len+1)-1)).
Proof.
  remember (2^len-1) as v1.
  replace (2^len) with (v1+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply ROv.
  subst.
  applys_eq (RIncs len (2^len-1)); flia.
Qed.

Definition S' '(lenL,lenR,n) := LC lenL 0 <| RC lenR (2^lenR-1-n).

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep lenL lenR n lenR' n':
  n<2^lenR ->
  sideRLs tm (hRL^^(2^lenL*2-1)) (RC' lenR (2^lenR-1-n)) (RC lenR' (2^lenR'-1-n')) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR',n').
Proof.
  unfold S'.
  intros.
  rewrite (Rshift lenR) by lia.
  follow LOv.
  epose proof (sideRLs_concat) as I1.
  erewrite lrcons_lpow1 in I1.
  2: shelve.
  epose proof (LIncs _ (2^lenL*2-1-1) _) as I2.
  specialize (I1 I2 H0).
  applys_eq I1;
  unfold to_DH_config; flia.
  Unshelve.
  all: rw_pa; lia.
Qed.

Lemma BigStep1 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+n0 ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite Nat.add_comm.
  apply RIncs; lia.
Qed.

Lemma BigStep2 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^(lenR+1)+n0) ->
  n0<2^(lenR+1+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite (Nat.add_comm 1 lenR).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma BigStep0 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^lenR+n0) ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR+1,2^lenR+n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: rw_pa; lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs'' lenR n); rw_pa; flia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma init:
  c0 -->*
  S' (5,4,15).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(lenL,lenR,n) => n<2^lenR /\ lenR<>O /\ (lenL=lenR \/ lenL=lenR+1)).
  2: lia.
  intros [[lenL lenR] n] [I1 [I2 I3]].
  remember (lenR-1) as lenR'.
  replace lenR with (lenR'+1) in * by lia.
  destruct I3 as [I3|I3]; subst lenL.
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1)*2-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1) lenR' (n-2^lenR') (2^lenR'*6-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep2 with (n0:=2^(lenR'+1+1)-1-(n*3+1)).
      all: rw_pa; lia. }
    destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)*2-1)) as [E0|E0].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1+1) lenR' (n-2^lenR') (2^lenR'*10-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
Qed.

End TM2.


Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0RF_0RC0LB_1LD1RE_1LB0LA_1RA1LA_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation rd0' := [0;1;1;0].
Notation rd1' := [0;0;1;0].
Notation rd0 := [0;0;1;1].
Notation rd1 := [0;0;0;1].

Notation hR := (E,[1]).
Notation hL := (B,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{B}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{E}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Lemma LOv len r:
  LC len 0 <| [0] *> r -->*
  LC (len+1) ((2^len-1)*2) |> r.
Proof.
  unfold LC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Definition RC len n := BinDec rd0 rd1 len n 0inf.
Definition RC' len n := BinDec rd0' rd1' len n 0inf.

Lemma RInc l len n:
  1+n<2^len ->
  l |> RC len (1+n) -->+
  l <| RC len n.
Proof.
  intros.
  eapply RBinDec_spec.
  2: lia.
  es.
Qed.

Lemma RIncs len n:
  n<2^len ->
  sideRLs tm (hRL^^n) (RC len (2^len-1)) (RC len (2^len-1-n)).
Proof.
  induction n; intros.
  - applys_eq sideRLseq_O; flia.
  - replace (S n) with (n+1) by lia.
    rewrite lpow_add.
    eapply sideRLs_trans.
    1: apply IHn; lia.
    econstructor.
    2: constructor.
    intro.
    applys_eq (RInc l len (2^len-1-(n+1))).
    2: lia.
    unfold to_DH_config; flia.
Qed.

Lemma Rshift len n:
  n<2^len ->
  RC len n =
  [0] *> RC' len n.
Proof.
  unfold RC,RC'.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    cbn.
    solve_const0_eq.
  - cbn[Nat.pow] in *.
    replace (S len) with (len+1) by lia.
    divmod2_cases n;
    rw_Bin; solve_pow2_lt;
    rewrite IHlen by lia;
    reflexivity.
Qed.

Lemma RIncs' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' len (2^len-1-n)) (RC (1+len) (2^(1+len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      rewrite <-lpow_add'.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (S len) with (len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma RIncs'' len n:
  n<2^len ->
  sideRLs tm (hRL^^(n*3+1)) (RC' (1+len) (2^len-1-n)) (RC (len) (2^(len)-1)).
Proof.
  unfold RC',RC.
  rw_Bin.
  gen n.
  induction len; intros.
  - replace n with O by lia.
    esx.
    es.
  - cbn[Nat.pow] in *.
    divmod2_cases n.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-n'*2) with ((2^len-1-n')*2+1) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace (n'*2*3) with (n'*3*2) by lia.
      eapply segRLs_addmul; esx.
    + unshelve epose proof (IHlen n' _) as H0.
      1: lia.
      cbn[lpow].
      rewrite Str_app_assoc.
      replace (2*2^len-1-(n'*2+1)) with ((2^len-1-n')*2) by lia.
      replace (1+S len) with (1+len+1) by lia.
      rw_Bin; solve_pow2_lt.
      eapply segRLs_sideRLs_concat.
      2: applys_eq H0; flia.
      replace ((n'*2+1)*3+1) with ((n'*3)*2+4) by lia.
      eapply segRLs_addmul; esx.
Qed.

Lemma ROv len:
  sideRLs tm hRL (RC len 0) (RC (len+1) (2^(len+1)-1)).
Proof.
  unfold RC.
  rw_Bin.
  esx.
Qed.

Lemma RIncsOv len:
  sideRLs tm (hRL^^(2^len)) (RC len (2^len-1)) (RC (len+1) (2^(len+1)-1)).
Proof.
  remember (2^len-1) as v1.
  replace (2^len) with (v1+1) by lia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  2: apply ROv.
  subst.
  applys_eq (RIncs len (2^len-1)); flia.
Qed.

Definition S' '(lenL,lenR,n) := LC lenL 0 <| RC lenR (2^lenR-1-n).

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep lenL lenR n lenR' n':
  n<2^lenR ->
  sideRLs tm (hRL^^(2^lenL*2-1)) (RC' lenR (2^lenR-1-n)) (RC lenR' (2^lenR'-1-n')) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR',n').
Proof.
  unfold S'.
  intros.
  rewrite (Rshift lenR) by lia.
  follow LOv.
  epose proof (sideRLs_concat) as I1.
  erewrite lrcons_lpow1 in I1.
  2: shelve.
  epose proof (LIncs _ (2^lenL*2-1-1) _) as I2.
  specialize (I1 I2 H0).
  applys_eq I1;
  unfold to_DH_config; flia.
  Unshelve.
  all: rw_pa; lia.
Qed.

Lemma BigStep1 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+n0 ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite Nat.add_comm.
  apply RIncs; lia.
Qed.

Lemma BigStep2 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^(lenR+1)+n0) ->
  n0<2^(lenR+1+1) ->
  S' (lenL,lenR,n) -->+
  S' (lenL+1,lenR+1+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply (RIncs' lenR n); lia.
  rewrite (Nat.add_comm 1 lenR).
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma BigStep0 lenL lenR n n0:
  n<2^lenR ->
  2^lenL*2-1 = n*3+1+(2^lenR+n0) ->
  n0<2^(lenR+1) ->
  S' (lenL,lenR+1,2^lenR+n) -->+
  S' (lenL+1,lenR+1,n0).
Proof.
  intros.
  eapply BigStep.
  1: rw_pa; lia.
  rewrite H0.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: applys_eq (RIncs'' lenR n); rw_pa; flia.
  rewrite lpow_add.
  eapply sideRLs_trans.
  1: apply RIncsOv.
  apply RIncs; lia.
Qed.

Lemma init:
  c0 -->*
  S' (5,5,2).
Proof.
  esx.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(lenL,lenR,n) => n<2^lenR /\ lenR<>O /\ (lenL=lenR \/ lenL=lenR+1)).
  2: lia.
  intros [[lenL lenR] n] [I1 [I2 I3]].
  remember (lenR-1) as lenR'.
  replace lenR with (lenR'+1) in * by lia.
  destruct I3 as [I3|I3]; subst lenL.
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1)*2-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1) lenR' (n-2^lenR') (2^lenR'*6-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
  - destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)-1)) as [E|E].
    { eexists (_,_,_); split.
      1: apply BigStep2 with (n0:=2^(lenR'+1+1)-1-(n*3+1)).
      all: rw_pa; lia. }
    destruct (Nat.leb_spec (n*3+1) (2^(lenR'+1+1)*2-1)) as [E0|E0].
    { eexists (_,_,_); split.
      1: apply BigStep1 with (n0:=2^(lenR'+1+1)*2-1-(n*3+1)).
      all: rw_pa; lia. }
    { eexists (_,_,_); split.
      1: applys_eq (BigStep0 (lenR'+1+1) lenR' (n-2^lenR') (2^lenR'*10-2-n*3)).
      1: flia.
      all: rw_pa; lia. }
Qed.

End TM3.


Module TM4.

Definition tm := Eval compute in (TM_from_str "1LB0LE_0RC0LB_1LA1RD_1RE1LE_1RB0RF_---1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation ld0 := <[0;1].
Notation ld1 := <[1;0].
Notation hR := (D,[1]).
Notation hL := (B,[0]).
Notation hRL := [(hR,hL)].
Notation hLR := [(hL,hR)].

Notation "l <| r" := (l <{{B}} [0] *> r) (at level 30).
Notation "l |> r" := (l <* [1] {{D}}> r) (at level 30).

Definition LC len n := BinDec ld0 ld1 len n 0inf.

Lemma LInc len n r:
  1+n<2^len ->
  LC len (n+1) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  rewrite (lowbit_split x i len) by lia.
  epose proof (lowbit_split_lt x i len).
  rw_Bin; solve_pow2_lt.
  remember (len-i-1) as len'.
  assert (x=2^len'-1\/x<2^len'-1) as [E|E] by lia.
  - subst x.
    rw_Bin.
    es.
  - lowbitS_cases x.
    rewrite (lowbit_split x0 i0 len') by lia.
    epose proof (lowbit_split_lt x0 i0 len').
    rw_Bin; solve_pow2_lt.
    es.
Qed.

Lemma LIncs len n:
  n<2^len ->
  sideRLs (flip tm) (hLR^^n) (LC len n) (LC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    eapply sideRLs_trans.
    2: apply IHn; lia.
    econstructor.
    2: constructor.
    replace (S n) with (n+1) by lia.
    unfold sideRL; intros.
    epose proof (LInc _ _ _ H) as I1.
    apply flip_progress in I1.
    apply I1.
Qed.

Lemma LOv len r:
  LC len 0 <| [0] *> r -->*
  LC (len+1) ((2^len-1)*2) |> r.
Proof.
  unfold LC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Lemma lrcons_hLR n:
  lrcons hR (hLR^^n) hL = hRL^^(1+n).
Proof.
  induction n; cbn; trivial.
  rewrite IHn; trivial.
Qed.

Lemma BigStep len r r':
  sideRLs tm (hRL^^(2^len*2-1)) r ([0]*>r') ->
  LC len 0 <| [0] *> r -->+
  LC (len+1) 0 <| [0] *> r'.
Proof.
  intros.
  follow LOv.
  epose proof (LIncs (len+1) ((2^len-1)*2) ltac:(rewrite Nat.pow_add_r; lia)) as I1.
  epose proof (sideRLs_concat I1) as I2.
  rewrite lrcons_hLR in I2.
  apply I2.
  applys_eq H; flia.
Qed.

Inductive RD := D0|D1|W0|W1.

Fixpoint toRC r :=
match r with
| [] => 0inf
| D0::r => [0;1;1;0]*>toRC r
| D1::r => [0;0;1;0]*>toRC r
| W0::r => [0;1;1;1;1;0;0;0;1;0]*>toRC r
| W1::r => [0;0;1;1;1;0;0;0;1;0]*>toRC r
end.

Inductive RIncs: (list RD)->(list RD)->nat->Prop :=
| RIncs_D0_0 r r' n:
  RIncs r r' (1+n) ->
  RIncs (D0::r) (D0::r') (1+n*2)
| RIncs_D0_1 r r' n:
  RIncs r r' (1+n) ->
  RIncs (D0::r) (D1::r') (2+n*2)
| RIncs_D1_0 r r' n:
  RIncs r r' (n) ->
  RIncs (D1::r) (D0::r') (2+n*2)
| RIncs_D1_1 r r' n:
  RIncs r r' (n) ->
  RIncs (D1::r) (D1::r') (3+n*2)
| RIncs_W0_0 r r' n:
  RIncs r r' n ->
  RIncs (W0::r) (W0::r') (2+n*2)
| RIncs_W0_1 r r' n:
  RIncs r r' n ->
  RIncs (W0::r) (W1::r') (3+n*2)
| RIncs_W1_0 r r' n:
  RIncs r r' n ->
  RIncs (W1::r) (W0::r') (4+n*2)
| RIncs_W1_1 r r' n:
  RIncs r r' n ->
  RIncs (W1::r) (W1::r') (5+n*2)
| RIncs_O_1 r n:
  RIncs [] r n ->
  RIncs [] (D0::r) (1+n*2)
| RIncs_O_2 r n:
  RIncs [] r n ->
  RIncs [] (D1::r) (2+n*2)
| RIncs_O_0:
  RIncs [] [] 0
.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity).

Ltac ec := econstructor.

Ltac am a a' k b b' :=
  applys_eq (segRLs_addmul_v2 a a' k b b'); unfold DH0; flia; esc.

Ltac cat10 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_;_;_;_;_;_;_]) (w2:=[_;_;_;_;_;_;_;_;_;_]); [|eauto 1].

Ltac cat4 :=
  eapply @segRLs_sideRLs_concat with (w1:=[_;_;_;_]) (w2:=[_;_;_;_]); [|eauto 1].

Ltac cat4' :=
  do 4 rewrite const_unfold; cat4.

Close Scope sym.

Lemma RIncs_spec r r' n:
  RIncs r r' n ->
  sideRLs tm (hRL^^n) (toRC r) ([0%sym]*>toRC r').
Proof.
  intro H.
  induction H; cbn[toRC] in *.
  - cat4. am 2 1 n 1 1.
  - cat4. am 2 1 n 2 1.
  - cat4. am 2 1 n 2 0.
  - cat4. am 2 1 n 3 0.
  - cat10. am 2 1 n 2 0.
  - cat10. am 2 1 n 3 0.
  - cat10. am 2 1 n 4 0.
  - cat10. am 2 1 n 5 0.
  - cat4'. am 2 1 n 1 0.
  - cat4'. am 2 1 n 2 0.
  - esx.
Qed.

Open Scope sym.

Definition S' '(k,r) := LC k 0 <| [0]*>toRC r.

Lemma BigStep' k r r':
  RIncs r r' (2^k*2-1) ->
  S' (k,r) -->+
  S' (k+1,r').
Proof.
  unfold S'.
  intro H.
  apply RIncs_spec in H.
  apply BigStep,H.
Qed.

Lemma init:
  c0 -->*
  S' (7,[D0;D0;D0;W0;D0;D1;D1]).
Proof.
  esx.
Qed.

Inductive RWF: nat->(list RD)->Prop :=
| RWF_O:
  RWF 0 []
| RWF_O':
  RWF 1 []
| RWF_D0 i r:
  RWF i r ->
  RWF (S i) (D0::r)
| RWF_D1 i r:
  RWF i r ->
  RWF (S i) (D1::r)
.

Lemma RWF_spec i r k:
  RWF i r ->
  2^i*2-2<=k<=2^i*2 ->
  exists r',
  RIncs r r' k /\ RWF (S i) r'.
Proof.
  intro H.
  gen k.
  induction H; intros.
  { destruct k as [|[|[|]]]. 4: lia.
    + ec; ec.
      1: ec.
      ec.
    + ec; ec.
      1: apply RIncs_O_1 with (n:=O); ec.
      ec; ec.
    + ec; ec.
      1: apply RIncs_O_2 with (n:=O); ec.
      ec; ec. }
  { assert (k=2\/k=3\/k=4) as [E|[E|E]] by lia; subst.
    + ec; ec.
      1: apply RIncs_O_2 with (n:=O); ec.
      ec; ec.
    + ec; ec.
      1: apply RIncs_O_1 with (n:=1%nat).
      1: apply RIncs_O_1 with (n:=O); ec.
      ec; ec; ec.
    + ec; ec.
      1: apply RIncs_O_2 with (n:=1%nat).
      1: apply RIncs_O_1 with (n:=O); ec.
      ec; ec; ec. }
  1,2: cbn[Nat.pow] in *.
  2: assert (k=2+(2^i*2-2)*2\/k=3+(2^i*2-2)*2\/k=2+(2^i*2-1)*2) as [E|[E|E]] by lia; subst.
  1: assert (k=2+(2^i*2-2)*2\/k=1+(2^i*2-1)*2\/k=2+(2^i*2-1)*2) as [E|[E|E]] by lia; subst.
  all: epose proof (IHRWF _ _) as [r' [I1 I2]];
      ec; ec; ec; eauto 1.
  Unshelve.
  all: lia.
Qed.

Inductive RWF': nat->(list RD)->Prop :=
| RWF'_0 i r:
  RWF i r ->
  RWF' (4+i) (D0::D0::D0::W0::r)
| RWF'_1 i r:
  RWF i r ->
  RWF' (4+i) (D0::D1::D1::W0::r)
| RWF'_2 i r:
  RWF i r ->
  RWF' (4+i) (D0::D0::D1::W0::r)
| RWF'_3 i r:
  RWF i r ->
  RWF' (4+i) (D0::D1::D0::W1::r)
.

Lemma RWF'_spec i r:
  RWF' i r ->
  exists r',
  RIncs r r' (2^i*2-1) /\ RWF' (S i) r'.
Proof.
  intro H.
  induction H.
  - replace (2^(4+i)*2-1) with (1+(1+(1+(1+(2^i*2-1)*2)*2)*2)*2) by (cbn; lia).
    eapply RWF_spec in H.
    2: shelve.
    destruct H as [r' [I1 I2]].
    ec; ec.
    + do 4 ec.
      apply I1.
    + apply RWF'_1,I2.
  - replace (2^(4+i)*2-1) with (1+(1+(1+(3+(2^i*2-2)*2)*2)*2)*2) by (cbn; lia).
    eapply RWF_spec in H.
    2: shelve.
    destruct H as [r' [I1 I2]].
    ec; ec.
    + do 4 ec.
      apply I1.
    + apply RWF'_2,I2.
  - replace (2^(4+i)*2-1) with (1+(1+(1+(3+(2^i*2-2)*2)*2)*2)*2) by (cbn; lia).
    eapply RWF_spec in H.
    2: shelve.
    destruct H as [r' [I1 I2]].
    ec; ec.
    + do 4 ec.
      apply I1.
    + apply RWF'_3,I2.
  - replace (2^(4+i)*2-1) with (1+(1+(1+(3+(2^i*2-2)*2)*2)*2)*2) by (cbn; lia).
    eapply RWF_spec in H.
    2: shelve.
    destruct H as [r' [I1 I2]].
    ec; ec.
    + do 4 ec.
      apply I1.
    + apply RWF'_0,I2.
  Unshelve.
  all: lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=fun '(k,r) => RWF' k r).
  2: repeat ec.
  intros [k r] HP.
  eapply RWF'_spec in HP.
  destruct HP as [r' [I1 I2]].
  eapply BigStep' in I1.
  ec; ec.
  1: apply I1.
  cbn.
  applys_eq I2; flia.
Qed.

End TM4.


