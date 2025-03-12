From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import Lia PeanoNat String.

Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC' len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> BinInc rd1 m). 

Module V1.
Section V1.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Hypothesis x0: Config.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).

Hypothesis LInc:
  forall l r n,
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.

Hypothesis RInc:
  forall l r n,
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.

Hypothesis LOv:
  forall r n,
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.

Hypothesis ROv:
  forall l r n,
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1^^n <| [1] *> r.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; assumption.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  intros.
  apply RInc.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; assumption.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR) <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  2: rewrite pow2_S; lia.
  2:{
    rewrite Nat.pow_add_r.
    apply Nat.mul_lt_mono_pos_r.
    2: rewrite pow2_S; lia.
    pose proof (Nat.pow_nonzero 2 lenR); lia.
  }
  follow10 ROv.
  rw_Bin.
  cbn.
  finish.
Qed.

Lemma RC'_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  rw_Bin.
  2: rewrite pow2_S; lia.
  2:{
    rewrite Nat.pow_add_r.
    apply Nat.mul_lt_mono_pos_r.
    2: rewrite pow2_S; lia.
    pose proof (Nat.pow_nonzero 2 lenR); lia.
  }
  follow10 ROv.
  rw_Bin.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\ (lenR=O -> n=O -> m=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      pose proof (Nat.pow_nonzero 2 i).
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      repeat split; try lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgL _ _ _). split.
        1: apply RC'_Ov_0; lia.
        pose proof (Nat.pow_nonzero 2 lenR).
        repeat split; try lia.
        rewrite Nat.pow_add_r.
        rewrite pow2_S in *.
        destruct lenR; cbn[Nat.pow] in *; try lia.
        assert ((k*2+1)*2^lenR < 2^lenL*2*2^lenR).
        1: apply Nat.mul_lt_mono_pos_r; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC'_Ov; lia.
        pose proof (Nat.pow_nonzero 2 i).
        rewrite pow2_S in *.
        pose proof (split_bound_v2 x i).
        repeat split; try lia.
        -- apply le_pow2_v1.
           lia.
        -- rewrite Nat.pow_add_r.
           apply Nat.mul_lt_mono_pos_r.
           2: rewrite pow2_S; lia.
           lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  1: apply closed.
  apply Pinit.
Qed.

End V1.
End V1.

Module V2.
Section V2.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Hypothesis x0: Config.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).

Hypothesis LInc:
  forall l r n,
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.

Hypothesis RInc:
  forall l r n,
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.

Hypothesis LOv:
  forall r n,
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.

Hypothesis ROv:
  forall l r n,
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n <| [1] *> r.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; assumption.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  intros.
  apply RInc.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; assumption.
Qed.

Lemma RC'_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  pose proof (Nat.pow_nonzero 2 lenR).
  rw_Bin.
  2:{
    rewrite Nat.pow_add_r,pow2_S.
    assert ((k*2+1)*2^lenR<2^lenL*2*2^lenR) by (apply Nat.mul_lt_mono_pos_r; try lia).
    lia.
  }
  follow10 ROv.
  rw_Bin.
  cbn.
  finish.
Qed.

Lemma RC'_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  pose proof (Nat.pow_nonzero 2 lenR).
  rw_Bin.
  2:{
    rewrite Nat.pow_add_r,pow2_S.
    assert ((k*2+1)*2^lenR<2^lenL*2*2^lenR) by (apply Nat.mul_lt_mono_pos_r; try lia).
    lia.
  }
  follow10 ROv.
  rw_Bin.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      pose proof (Nat.pow_nonzero 2 i).
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      repeat split; try lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgL _ _ _). split.
        1: apply RC'_Ov_0; lia.
        pose proof (Nat.pow_nonzero 2 lenR).
        repeat split; try lia.
        rewrite Nat.pow_add_r.
        rewrite pow2_S in *.
        destruct lenR; cbn[Nat.pow] in *; try lia.
        assert ((k*2+1)*2^lenR < 2^lenL*2*2^lenR).
        1: apply Nat.mul_lt_mono_pos_r; lia.
        lia.
      * eexists (cfgL' _ _ _ _ _). split.
        1: apply RC'_Ov; lia.
        pose proof (Nat.pow_nonzero 2 i).
        rewrite pow2_S in *.
        pose proof (split_bound_v2 x i).
        repeat split; try lia.
        -- apply lt_le_sub1.
           apply lt_pow2_v1.
           lia.
        -- rewrite Nat.pow_add_r.
           apply lt_sub1.
           apply Nat.mul_lt_mono_pos_r.
           2: rewrite pow2_S; lia.
           lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  1: apply closed.
  apply Pinit.
Qed.

End V2.
End V2.

Module V3.
Section V3.
Hypothesis tm:TM.
Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL'(lenL k lenR n m:nat)
| cfgR'(lenL k lenR n m:nat)
.

Hypothesis x0: Config.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).

Hypothesis LInc:
  forall l r n,
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.

Hypothesis RInc:
  forall l r n,
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.

Hypothesis LOv:
  forall r n,
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.

Hypothesis ROv_S:
  forall l r n,
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n <| [1] *> r.

Hypothesis ROv_O:
  forall l r n,
  l <* ld0 <* ld1^^n |> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> r.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; assumption.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  intros.
  apply RInc.
Qed.

Lemma RC'_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) m -->+
  l <| RC' len n m.
Proof.
  intros H.
  apply RBinDec2_spec; assumption.
Qed.

Lemma RC'_Ov_S lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC' (lenR+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) <| RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  pose proof (Nat.pow_nonzero 2 lenR).
  rw_Bin.
  2: rewrite pow2_S; lia.
  2:{
    rewrite Nat.pow_add_r.
    repeat rewrite pow2_S.
    apply lt_sub1.
    apply Nat.mul_lt_mono_pos_r; lia.
  }
  rewrite Nat.add_comm.
  follow10 ROv_S.
  rw_Bin.
  cbn.
  finish.
Qed.

Lemma RC'_Ov_S_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC' (lenR+1) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) <| RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  pose proof (Nat.pow_nonzero 2 lenR).
  rw_Bin.
  2: rewrite pow2_S; lia.
  2:{
    rewrite Nat.pow_add_r.
    repeat rewrite pow2_S.
    apply lt_sub1.
    apply Nat.mul_lt_mono_pos_r; lia.
  }
  rewrite Nat.add_comm.
  follow10 ROv_S.
  rw_Bin.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Lemma mul_lt_r a b c:
  a*c < b*c ->
  c<>O ->
  a<b.
Proof.
  induction c; lia.
Qed.

Lemma lowbit_lb x i n:
  (x*2+1)*2^i < 2^n ->
  i+1<=n.
Proof.
  gen n.
  induction i; intros.
  - cbn in H.
    destruct n as [|n].
    2: lia.
    cbn in H.
    lia.
  - destruct n as [|n].
    + pose proof (Nat.pow_nonzero 2 i).
      cbn in H; lia.
    + specialize (IHi n).
      cbn in H,IHi.
      lia.
Qed.


Lemma RC'_Ov_O lenL k i m:
  S k<2^lenL ->
  LC lenL (S k) |> RC' 0 0 ((m*2+1)*2^i) -->+
  LC (lenL+1) (k*2+1) |> RC' i ((2^i-1)*2) m.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  lowbit_cases (S k).
  replace (k*2) with (((x*2+1)*2^i0-1)*2) by lia.
  pose proof (lowbit_lb x i0 lenL).
  replace (lenL) with (lenL-i0-1+1+i0) in * by lia.
  rw_Bin.
  2:lia.
  2:{
    rewrite <-H0 in Hk.
    rewrite Nat.pow_add_r in Hk.
    eapply mul_lt_r.
    apply Hk.
    lia.
  }
  2:lia.
  2:{
    rewrite pow2_S.
    lia.
  }
  follow10 ROv_O.
  rw_Bin.
  cbn.
  finish.
Qed.

Lemma RC'_Ov_O_0 lenL k:
  S k<2^lenL ->
  LC lenL (S k) |> RC' 0 0 0 -->+
  LC (lenL+1) (k*2+1) |> RC 1.
Proof.
  intros Hk.
  unfold LC,RC,RC'.
  lowbit_cases (S k).
  replace (k*2) with (((x*2+1)*2^i-1)*2) by lia.
  pose proof (lowbit_lb x i lenL).
  replace (lenL) with (lenL-i-1+1+i) in * by lia.
  rw_Bin.
  2:lia.
  2:{
    rewrite <-H0 in Hk.
    rewrite Nat.pow_add_r in Hk.
    eapply mul_lt_r.
    apply Hk.
    lia.
  }
  2:lia.
  2:{
    rewrite pow2_S.
    lia.
  }
  follow10 ROv_O.
  rw_Bin.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC' i ((2^i-1)*2) n.
Proof.
  unfold LC,RC,RC'.
  rw_Bin.
  follow10 LOv.
  cbn.
  repeat rewrite <-const_unfold.
  finish.
Qed.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL' lenL k lenR n m => LC lenL k <| RC' lenR n m
| cfgR' lenL k lenR n m => LC lenL k |> RC' lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL
| cfgL' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ (lenR=O -> m=O -> n+2<=k)
| cfgR' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\ (lenR=O -> m=O -> n+1<=k)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eexists (cfgR' _ _ _ _ _). split.
      1: apply LC_Ov.
      pose proof (Nat.pow_nonzero 2 i).
      rewrite pow2_S.
      pose proof (split_bound_v1 x i lenL).
      repeat split; try lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR' _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * destruct lenR as [|lenR].
        -- destruct k as [|k].
           1: lia.
           eexists (cfgR _ _ _). split.
           1: apply RC'_Ov_O_0; lia.
           rewrite pow2_S.
           lia.
        -- replace (S lenR) with (lenR+1) by lia.
           eexists (cfgL _ _ _). split.
           1: apply RC'_Ov_S_0; lia.
           pose proof (Nat.pow_nonzero 2 lenR).
           repeat split; try lia.
           rewrite Nat.pow_add_r.
           rewrite Nat.sub_add. 2: lia.
           repeat rewrite pow2_S.
           apply Nat.mul_lt_mono_pos_r; lia.
      * destruct lenR as [|lenR].
        -- destruct k as [|k].
           1: lia.
           eexists (cfgR' _ _ _ _ _). split.
           1: apply RC'_Ov_O; lia.
           pose proof (Nat.pow_nonzero 2 i).
           pose proof (split_bound_v2 x i).
           repeat rewrite pow2_S.
           repeat split; try lia.
        -- replace (S lenR) with (lenR+1) in * by lia.
           eexists (cfgL' _ _ _ _ _). split.
           1: apply RC'_Ov_S; lia.
           pose proof (Nat.pow_nonzero 2 i).
           pose proof (split_bound_v2 x i).
           repeat rewrite pow2_S in *.
           repeat split; try lia.
           ++ apply lt_le_sub1.
              apply lt_pow2_v1.
              lia.
           ++ rewrite Nat.pow_add_r.
              repeat rewrite pow2_S.
              apply lt_sub1.
              apply Nat.mul_lt_mono_pos_r; lia.
           ++ intros.
              subst i x.
              cbn; lia.
    + eexists (cfgL' _ _ _ _ _). split.
      1: apply RC'_Inc; lia.
      lia.
Qed. 

Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond.
  1: apply closed.
  apply Pinit.
Qed.

End V3.
End V3.

Transparent BinDec BinDec2 BinInc.

Ltac solve_v1 QL QR qL qR lenL n :=
  eapply (V1.nonhalt _ QL QR qL qR (V1.cfgL lenL 0 n));
  [ try (es; fail)
  | try (es; fail)
  | try (solve_LOverflow; fail)
  | try (es; fail)
  | try (cbn; solve_init)
  | try (cbn; lia) ].

Ltac solve_v2 QL QR qL qR lenL n :=
  eapply (V2.nonhalt _ QL QR qL qR (V2.cfgL lenL 0 n));
  [ try (es; fail)
  | try (es; fail)
  | try (solve_LOverflow; fail)
  | try (es; fail)
  | try (cbn; solve_init)
  | try (cbn; lia) ].

Ltac solve_v3 QL QR qL qR lenL n :=
  eapply (V3.nonhalt _ QL QR qL qR (V3.cfgL lenL 0 n));
  [ es
  | es
  | solve_LOverflow
  | es
  | solve_LOverflow
  | try (cbn; solve_init)
  | try (cbn; lia) ].

Lemma tm1: ~halts (TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_1LC---") c0.
Proof.
  solve_v1 E C [0;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm2: ~halts (TM_from_str "1RB0LE_1LC1RF_0LD0LC_1RD0RA_1RC---_1RA0RA") c0.
Proof.
  solve_v1 D B [0;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm3: ~halts (TM_from_str "1LB0LF_1LC1RD_0LD0LC_1RE0RF_1RB---_0RA1RB") c0.
Proof.
  solve_v1 D B [0;1;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm4: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0RA_---1LB") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm5: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0RA_---0LE") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm6: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0LD_---1LB") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm7: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0RA0LD_---0LE") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm8: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_1RB0RA_---1LB") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm9: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_1LD0RA_---1LB") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm10: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC1RE_0RA0RA_---0LE") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm11: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC1RE_1LD0RA_---0LE") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm12: ~halts (TM_from_str "1RB0RE_1LC0LB_1RE1RD_---0LA_1LB1RF_1RC1RA") c0.
Proof.
  solve_v1 C E [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm13: ~halts (TM_from_str "1RB0RB_1RC0LF_1LD1RA_0LE0LD_1RE0RB_0RB---") c0.
Proof.
  solve_v1 E C [0;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm14: ~halts (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB0RF_1LA---") c0.
Proof.
  solve_v1 D B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm15: ~halts (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1LA---") c0.
Proof.
  solve_v1 D B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm16: ~halts (TM_from_str "1RB1RB_1LC1RD_1LD0LC_1RE0RA_1RB1RF_1RD---") c0.
Proof.
  solve_v1 D B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm17: ~halts (TM_from_str "1RB1RB_1LC0LE_1LD0LC_1RE0RA_1RB1RF_1RD---") c0.
Proof.
  solve_v1 D B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm18: ~halts (TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RA_1RF0RA_1RB---") c0.
Proof.
  solve_v1 D B [0;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm19: ~halts (TM_from_str "1LB1LB_1LC1RD_0LD0LC_1RE0RF_1RB---_0RA1RB") c0.
Proof.
  solve_v1 D B [0;1;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm20: ~halts (TM_from_str "1RB1RC_0LA---_1LD1RF_1LE0LD_1RC0RA_1RE0RA") c0.
Proof.
  solve_v1 E C [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm21: ~halts (TM_from_str "1LB1LC_0RA1RC_1LD1RE_0LE0LD_1RF0RB_1RC---") c0.
Proof.
  solve_v1 E C [0;1;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm22: ~halts (TM_from_str "1RB0RE_1LC1RD_1LA0LC_1RA0RE_0RF1RB_0LA---") c0.
Proof.
  solve_v1 A B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm23: ~halts (TM_from_str "1RB0RE_1LC1RD_1LD0LC_1RA0RF_1LA---_1RB1RB") c0.
Proof.
  solve_v1 D B [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm24: ~halts (TM_from_str "1RB1RE_1LC---_1LD0LC_1RE0RA_1LC1RF_1RD0RA") c0.
Proof.
  solve_v1 D E [1;0;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm25: ~halts (TM_from_str "1RB0RD_1LC0LB_1RD1LC_1LB1RE_1RF1RA_1RD---") c0.
Proof.
  solve_v1 C D [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm26: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_1LB---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm27: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_1LD---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm28: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_1RF0RA_1LC---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm29: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_1RF0RA_0LE---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm30: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_0RA0RA_1RA---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm31: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_0RA0LD_1RA---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm32: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_1LD0RA_1RA---") c0.
Proof.
  solve_v1 C A [1;1;1] [0;1;1] 3 6.
Qed.

Lemma tm33: ~halts (TM_from_str "1RB1RB_1LC1RF_1RD0LC_1LE---_1RA1LE_0RD0RA") c0.
Proof.
  solve_v1 E B [1;1;1;1] [1;0;1;1] 3 6.
Qed.

Lemma tm34: ~halts (TM_from_str "1RB---_1LC1RF_0LD0LC_1RD1RE_0LE0RB_1RA1RE") c0.
Proof.
  solve_v2 D B [0;1;1] [0;1;1] 4 11.
Qed.

Lemma tm35: ~halts (TM_from_str "1RB---_1LC1RE_0LE0LD_1LB0LD_1RA0RF_1LC1RB") c0.
Proof.
  solve_v2 E B [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm36: ~halts (TM_from_str "1LB1RD_1RC0LB_0LD1RB_1RF0RE_1LC1RA_1RA---") c0.
Proof.
  solve_v2 D A [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm37: ~halts (TM_from_str "1LB1RD_1RC0LB_0LD0RD_1RE0RF_1RA---_1LC1RA") c0.
Proof.
  solve_v2 D A [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm38: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RE_1RF1RA_0LB---") c0.
Proof.
  solve_v2 C A [1;0;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm39: ~halts (TM_from_str "1RB0RE_1RC1RF_1LD1RA_0RE0LD_1LF1RC_0LA---") c0.
Proof.
  solve_v2 A C [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm40: ~halts (TM_from_str "1LB1RE_1RC0LB_0LE0RD_1RA---_1RD0RF_1LC1RA") c0.
Proof.
  solve_v2 E A [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm41: ~halts (TM_from_str "1RB0RF_1RC1RE_1LD1RA_1RE0LD_0LA---_1LE1RC") c0.
Proof.
  solve_v2 A C [0;1;1;1] [1;0;1;1] 4 11.
Qed.

Lemma tm42: ~halts (TM_from_str "1RB1RF_1RC---_1LD1RA_0LE0LD_1RE1RF_0LF0RC") c0.
Proof.
  solve_v2 E C [0;1;1] [0;1;1] 6 12.
Qed.

Lemma tm43: ~halts (TM_from_str "1RB0RF_1RC1RD_1LD1RA_1RE0LD_0LA---_1LE1RC") c0.
Proof.
  solve_v2 A C [0;1;1;1] [1;0;1;1] 6 12.
Qed.

Lemma tm44: ~halts (TM_from_str "1RB---_1LC1RF_1RD0LC_1LE1RB_0LF1LE_1RA0RD") c0.
Proof.
  solve_v3 F B [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 2 3.
Qed.

Lemma tm45: ~halts (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_0LD---_1LE1RB") c0.
Proof.
  solve_v3 D B [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 2 3.
Qed.

Lemma tm46: ~halts (TM_from_str "1LB---_1RC0LB_1LE1RD_1LB1RF_0LF1LE_0RA0RC") c0.
Proof.
  solve_v3 F D [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 4.
Qed.

Lemma tm47: ~halts (TM_from_str "1LB1RE_1RC0LB_1LD1RA_0LE1LD_1RF0RC_1RA---") c0.
Proof.
  solve_v3 E A [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 4.
Qed.

Lemma tm48: ~halts (TM_from_str "1RB0RF_1RC1RE_1LD1RA_1LA0LD_0LA---_1LE1RC") c0.
Proof.
  solve_v3 A C [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 4.
Qed.

Lemma tm49: ~halts (TM_from_str "1LB0LA_1RC0RE_1RF1RD_0LB---_1LD1RF_1LA1RB") c0.
Proof.
  solve_v3 B F [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 7.
Qed.

Lemma tm50: ~halts (TM_from_str "1RB0LA_1LC1RF_0LD1LC_0RE0RB_1LA---_1LA1RD") c0.
Proof.
  solve_v3 D F [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 7.
Qed.

Lemma tm51: ~halts (TM_from_str "1RB0LA_1LC1RF_0LD1LC_1RE0RB_1RF---_1LA1RD") c0.
Proof.
  solve_v3 D F [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 3 7.
Qed.

Lemma tm52: ~halts (TM_from_str "1LB1RE_0LC---_1RD0RA_1RE1RB_1LF1RC_1LC0LF") c0.
Proof.
  solve_v3 C E [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 4 7.
Qed.

Lemma tm53: ~halts (TM_from_str "1LB1RF_0LC1LB_0RD0RA_1LE---_1RA0LE_1LE1RC") c0.
Proof.
  solve_v3 C F [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 4 7.
Qed.

Lemma tm54: ~halts (TM_from_str "1LB1RE_0LC1LB_1RD0RA_1RE---_1LF1RC_1RA0LF") c0.
Proof.
  solve_v3 C E [0;1;1;1;1;1;1] [1;0;1;1;0;1;1] 4 7.
Qed.

Lemma tm55: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC0RE_0LB1RA_---1RA") c0.
Proof.
  solve_v2 C A [1;0;1;1] [1;0;1;1] 4 11.
  intros.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma tm56: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA0RF_1RC1RE_0LE1LC_---1RA") c0.
Proof.
  solve_v2 C A [1;0;1;1] [1;0;1;1] 4 11.
  intros.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.

Lemma tm57: ~halts (TM_from_str "1LB1RD_1LC0LB_1RA1RF_1RC0RE_0LB1RA_---1LD") c0.
Proof.
  solve_v2 C A [1;0;1;1] [1;0;1;1] 4 11.
  intros.
  change ([1;0;1;1] *> r) with ([1;0;1] *> [1] *> r).
  generalize ([1] *> r).
  es.
Qed.



