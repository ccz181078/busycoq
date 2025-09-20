From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat.
Require Import Lia PeanoNat String.
From BusyCoq Require Import ES_v2.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm1 := [1;1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0] len n (rd1 *> BinInc rd1 m). 
Definition RC2 len n m := BinDec2 [0] [1] [0;0;0] len n ([0;0] *> rd1 *> BinInc rd1 m). 

Ltac follow' H :=
  intros;
  epose proof H as HX;
  cbn[Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *;
  follow10 HX;
  repeat (simpl_rotate || simpl_tape);
  finish.

Ltac solve_rule H :=
  intros;
  unfold LC,RC,RC1,RC2;
  rw_Bin; try solve[solve_pow2_lt]; follow' H.


Ltac cbns :=
  cbn[app];
  cbv[BinaryCounter.d0];
  cbv[Datatypes.length];
  cbn[List.repeat].

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Ltac spl := repeat split; try lia; try solve[solve_pow2_lt].

Ltac eex f :=
  (eexists (f _ _ _ _ _ _) ||
  eexists (f _ _ _ _ _) ||
  eexists (f _ _ _ _) ||
  eexists (f _ _ _) ||
  eexists (f _ _) ||
  eexists (f _) ||
  eexists f); split.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  rw_pa.


Module TM101.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_0LD1RC_1RA1LD_1RF0RA_1RD---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0;0] *> r -->+
  l <| rd0^^n *> [1;0] *> r.
Proof.
  destruct n; es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma RInc' l r n:
  l |> rd1^^n *> [0;1;0;0;0] *> r -->+
  l <| rd0^^n *> rm1 *> r.
Proof.
  destruct n; es.
Qed.


Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  rewrite Nat.add_comm.
  intros H.
  unfold RC1.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  epose proof (lowbit_split x i (lenR+1)) as I1.
  epose proof (lowbit_split_lt x i (lenR+1)) as I2.
  remember (lenR+1-i-1) as lenR'.
  replace lenR with (lenR'+i) in * by lia.
  rw_Bin; solve_pow2_lt.
  destruct lenR'.
  - replace x with O by lia.
    rw_Bin.
    follow' RInc'.
  - replace (S lenR') with (lenR'+1) in * by lia.
    rw_pa.
    divmod2_cases x; rw_Bin; solve_pow2_lt; follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  rewrite Nat.add_comm.
  intros H.
  unfold RC2.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  epose proof (lowbit_split x i (lenR+1)) as I1.
  epose proof (lowbit_split_lt x i (lenR+1)) as I2.
  remember (lenR+1-i-1) as lenR'.
  replace lenR with (lenR'+i) in * by lia.
  rw_Bin; solve_pow2_lt.
  destruct lenR'.
  - replace x with O by lia.
    rw_Bin.
    follow' RInc.
  - replace (S lenR') with (lenR'+1) in * by lia.
    rw_pa.
    divmod2_cases x; rw_Bin; solve_pow2_lt; follow' RInc.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2) |> RC 1.
Proof.
  epose proof (ROv2 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgL2(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgL2 lenL k lenR n m => LC lenL k <| RC2 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=0 -> n=0 -> m=0 -> k+1 < 2^lenL)
| cfgL2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
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
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgR.
      1: apply LC_Inc; lia.
      lia.
  - eex cfgL.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR1.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC1_Ov_0; lia.
        spl.
        destruct lenR as [|lenR].
        1: rw_pa; lia.
        replace (S lenR*2) with (lenR*2+2) by lia.
        solve_v1 k lenL (lenR*2).
      * eex cfgR2.
        1: apply RC1_Ov; lia.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + eex cfgL1.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR2.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC2_Ov_0; lia.
        spl.
        solve_v1 k lenL (lenR*2).
      * eex cfgR2.
        1: apply RC2_Ov; lia.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL2.
      1: apply RC2_Inc; lia.
      lia.
Qed.
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM101.


Module TM102.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_0LB1RE_1RA0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{C}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0;0] *> r -->+
  l <| rd0^^n *> [1;0] *> r.
Proof.
  destruct n; es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma RInc' l r n:
  l |> rd1^^n *> [0;1;0;0;0] *> r -->+
  l <| rd0^^n *> rm1 *> r.
Proof.
  destruct n; es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  rewrite Nat.add_comm.
  intros H.
  unfold RC1.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  epose proof (lowbit_split x i (lenR+1)) as I1.
  epose proof (lowbit_split_lt x i (lenR+1)) as I2.
  remember (lenR+1-i-1) as lenR'.
  replace lenR with (lenR'+i) in * by lia.
  rw_Bin; solve_pow2_lt.
  destruct lenR'.
  - replace x with O by lia.
    rw_Bin.
    follow' RInc'.
  - replace (S lenR') with (lenR'+1) in * by lia.
    rw_pa.
    divmod2_cases x; rw_Bin; solve_pow2_lt; follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  rewrite Nat.add_comm.
  intros H.
  unfold RC2.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  epose proof (lowbit_split x i (lenR+1)) as I1.
  epose proof (lowbit_split_lt x i (lenR+1)) as I2.
  remember (lenR+1-i-1) as lenR'.
  replace lenR with (lenR'+i) in * by lia.
  rw_Bin; solve_pow2_lt.
  destruct lenR'.
  - replace x with O by lia.
    rw_Bin.
    follow' RInc.
  - replace (S lenR') with (lenR'+1) in * by lia.
    rw_pa.
    divmod2_cases x; rw_Bin; solve_pow2_lt; follow' RInc.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2) |> RC 1.
Proof.
  epose proof (ROv2 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgL2(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgL2 lenL k lenR n m => LC lenL k <| RC2 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=0 -> n=0 -> m=0 -> k+1 < 2^lenL)
| cfgL2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
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
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgR.
      1: apply LC_Inc; lia.
      lia.
  - eex cfgL.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR1.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC1_Ov_0; lia.
        spl.
        destruct lenR as [|lenR].
        1: rw_pa; lia.
        replace (S lenR*2) with (lenR*2+2) by lia.
        solve_v1 k lenL (lenR*2).
      * eex cfgR2.
        1: apply RC1_Ov; lia.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + eex cfgL1.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR2.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC2_Ov_0; lia.
        spl.
        solve_v1 k lenL (lenR*2).
      * eex cfgR2.
        1: apply RC2_Ov; lia.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL2.
      1: apply RC2_Inc; lia.
      lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM102.


Module TM179.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n m:
  l |> rd1^^n *> rm3 *> rd0^^m *> rd1 *> r -->+
  l <* ld0 <* ld1^^(n*2+2) <* ld0^^(m*2+1) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1] {{C}}> r) (at level 30).

Lemma ROv2_0 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld0 <* ld1^^(n*2+1) <* ld0 <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv' l r:
  l |2> rd0 *> r -->+
  l <* ld1^^2 |2> r.
Proof.
  es.
Qed.



Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_1 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((x*2+1)*2^i0*2+1)*2^i) -->+
  LC (lenL+1+(lenR*2+2)+(i*2+1)) (((k*2+1)*2^(lenR*2+2)+1)*2^(i*2+1)-1) |> RC2 i0 ((2^i0-1)*2) x.
Proof.
  intros.
  unfold LC,RC,RC2.
  remember (i*2+1) as i2.
  rw_Bin; solve_pow2_lt.
  subst.
  follow' ROv2.
Qed.

Lemma RC2_Ov_1_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i) -->+
  LC (lenL+1+(lenR*2+2)+(i*2+1)) (((k*2+1)*2^(lenR*2+2)+1)*2^(i*2+1)-1) |> RC 1.
Proof.
  intros.
  unfold LC,RC,RC2.
  remember (i*2+1) as i2.
  rw_Bin; solve_pow2_lt.
  subst.
  follow' ROv2.
Qed.

Lemma RC2_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+(lenR*2+1)+1+1) (((k*2+1)*2^(lenR*2+1)*2+1)*2) |2> 0inf.
Proof.
  epose proof (ROv2_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC_Ov2 lenL k:
  k<2^lenL ->
  LC lenL k |2> 0inf -->+
  LC (lenL+1+1) (k*2*2) |2> 0inf.
Proof.
  epose proof (ROv' _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR'(lenL k:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR' lenL k => LC lenL k |2> 0inf
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> m=O -> k+1 <> n+2^lenL)
| cfgR2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR' lenL k => k<2^lenL
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
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      destruct lenR as [|lenR].
      1: spl.
      replace (S lenR*2) with (lenR*2+2) by lia.
      solve_v1 k lenL (lenR*2).
    + eex cfgR2.
      1: apply RC1_Ov; lia.
      spl.
      pose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgR'.
      1: apply RC2_Ov_0; lia.
      spl.
    + lowbit_cases x.
      * eex cfgL.
        1: follow10 RC2_Ov_1_0; follow100 RC_Inc; finish.
        spl.
        assert ((k*2+1)*2^(lenR*2+2)+4<=2^(lenL+1+(lenR*2+2))) by (solve_v1 k lenL (lenR*2)).
        rewrite (Nat.pow_add_r 2 _ (i*2+1)) by lia.
        remember (2^(i*2+1)) as v1.
        remember ((k*2+1)*2^(lenR*2+2)) as v2.
        remember (2^(lenL+1+(lenR*2+2))) as v3.
        pose proof (Nat.mul_le_mono_pos_r (v2+4) v3 v1).
        lia.
      * eex cfgR2.
        1: apply RC2_Ov_1; lia.
        spl.
        1: zify_le_mul_r; lia.
        rewrite (Nat.pow_add_r 2 _ (i*2+1)) by lia.
        apply lt_add1mulpow2sub1.
        solve_pow2_lt.
  - eex cfgR'.
    1: apply RC_Ov2; lia.
    spl.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 21 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM179.


Module TM165.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_1RE1LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{C}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0 l r n:
  l |> rd1^^n *> rm3 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> rd1 *> [1;0;0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* <[1;0;1;1;1;0;1;1;1] {{B}}> r) (at level 30).

Lemma ROv2_1 l r n:
  l |> rd1^^n *> rm3 *> rd1 *> r -->+
  l <* ld0 <* ld1^^(n*2) <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld0 <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l <* ld1 <* ld0 |> rd0 *> [1;0;0] *> r.
Proof.
  es.
Qed.


Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0 lenL lenR k x i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2) |> RC2 (i+1) ((2^i-1)*2*2) x.
Proof.
  solve_rule ROv2_0.
Qed.

Lemma RC2_Ov_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (0*2) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2) |> RC 3.
Proof.
  epose proof (ROv2_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (m*2+1) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2))*2) |2> RC m.
Proof.
  solve_rule ROv2_1.
Qed.

Lemma RC'_1 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC (m*2+1) -->+
  LC (lenL+1+1) ((k*2+1)*2) |2> RC m.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC2 (i+1) ((2^i-1)*2*2+1) x.
Proof.
  solve_rule ROv'_0.
Qed.

Lemma RC'_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC 2.
Proof.
  epose proof (ROv'_0 _ 0inf) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR'(lenL k n:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR' lenL k n => LC lenL k |2> RC n
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> m=O -> k+1 < n+2^lenL)
| cfgR2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> m=O -> k+1 < n+2^lenL)
| cfgR' lenL k m => m<k<2^lenL /\
  (m=O -> k+1<2^lenL)
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
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      destruct lenR as [|lenR].
      1: spl.
      replace (S lenR*2) with (lenR*2+2) by lia.
      solve_v1 k lenL (lenR*2).
    + eex cfgR2.
      1: apply RC1_Ov; lia.
      spl.
      * pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
      * intros; subst.
        solve_v1 k lenL (lenR*2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases m.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC2_Ov_0_0; follow100 RC_Inc; finish.
        spl.
        destruct lenR as [|lenR].
        1: spl.
        replace (S lenR*2) with (lenR*2+2) by lia.
        solve_v1 k lenL (lenR*2).
      * eex cfgR2.
        1: apply RC2_Ov_0; lia.
        spl.
        solve_v1 k lenL (lenR*2).
    + eex cfgR'.
      1: apply RC2_Ov_1; lia.
      spl.
      * zify_le_mul_r; lia.
      * intros; subst.
        solve_v1 k lenL (lenR*2).
  - divmod2_cases n.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC'_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR2.
        1: apply RC'_0; lia.
        epose proof (split_bound_v2 x i).
        spl.
    + eex cfgR'.
      1: apply RC'_1; lia.
      spl.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM165.


Module TM31.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1LA1LB_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <| rd0^^n *> [0;0;0;1;1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;1;0;0] *> r -->+
  l <* ld1 <* ld0 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.


Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Definition RC3 len n m := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1;0;0] *> BinInc rd1 m). 

Lemma RC3_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC3 lenR (1+n) m -->+
  l <| RC3 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov l lenR m:
  l |> RC2 lenR 0 m -->+
  l <| RC3 lenR ((2^lenR-1)*2+1) m.
Proof.
  unfold RC3.
  solve_rule ROv2.
Qed.

Lemma RC3_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+(1+lenR*2)) ((k*2+1)*2^(1+lenR*2)-1) |> RC2 i ((2^i-1)*2) x.
Proof.
  unfold RC3.
  solve_rule ROv3.
Qed.

Lemma RC3_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 0 -->+
  LC (lenL+1+(1+lenR*2)) ((k*2+1)*2^(1+lenR*2)-1) |> RC 1.
Proof.
  unfold RC3.
  epose proof  (ROv3 _ 0inf _) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n x i:nat)
| cfgR1_0(lenL k lenR n:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n x i => LC lenL k |> RC1 lenR n ((x*2+1)*2^i)
| cfgR1_0 lenL k lenR n => LC lenL k |> RC1 lenR n 0
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n x i => n+(x*2+1)*2^i+1 <= k < 2^lenL /\ n<2^(lenR+1)
  /\ x+(2^i)*4<(((k-n)*2+1)*2^(lenR*2))
| cfgR1_0 lenL k lenR n => n+1 <= k < 2^lenL /\ n<2^(lenR+1)
  /\ (lenR=O -> k+1<n+2^lenL)
| cfgR2 lenL k lenR n m => n+m+1+2^lenR*2 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
      pose proof (split_bound_v1 x i lenL) as I1.
      lowbit_cases x.
      * eex cfgR1_0.
        1: apply LC_Ov.
        spl.
      * eex cfgR1.
        1: apply LC_Ov.
        spl.
        remember ((x0*2+1)*2^i0) as x1.
        eapply Nat.le_lt_trans with (m:=x1*4).
        1: epose proof (split_bound_v2 x0 (i0+1)); rw_pa; lia.
        clear Heqx1 x0 i0 I1.
        destruct x1.
        1: remember ((2 ^ lenL - 1 - (2 ^ i - 1) * 2)) as v1; lia.
        assert (i+2<=lenL) by (pp_pow2_lt_le (i+1) lenL; lia).
        remember (lenL-i-2) as lenL'.
        replace lenL with (lenL'+i+2) in * by lia.
        clear HeqlenL' lenL.
        assert ((x1*2+3)*2^i<2^lenL'*4*2^i) as I1 by (rw_pa; lia).
        rewrite <-Nat.mul_lt_mono_pos_r in I1 by lia.
        replace (2^(lenL'+i+2)-1-(2^i-1)*2) with ((2^lenL'*4-2)*2^i+1) by (rw_pa; lia).
        zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR2.
    1: apply RC1_Ov; lia.
    spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1_0.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgL.
    1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
    spl.
    destruct lenR.
    1: rw_pa; lia.
    replace (S lenR*2) with (lenR*2+2) by lia.
    solve_v1 k lenL (lenR*2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    destruct k. 1: lia.
    eex cfgR3.
    1: follow10 RC2_Ov; follow100 LC_Inc; finish.
    spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR3.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC3_Ov_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR2.
      1: apply RC3_Ov; lia.
      spl.
      epose proof (split_bound_v2 x (i+1)).
      rw_pa.
      rewrite Nat.mul_assoc.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM31.


Module TM254.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1LF_0LB1LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;0;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation ldh := (0inf <* <[1;1;1]).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(1+n) |> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) |> [0;0;0] *> r.
Proof.
  es.
Qed.

Definition LC len n := BinDec ld0 ld1 len n ldh.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  unfold LC.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.


Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2) n.
Proof.
  unfold LC.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  unfold LC.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  unfold LC.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  unfold LC.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  unfold LC.
  epose proof (ROv2 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgL2(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgL2 lenL k lenR n m => LC lenL k <| RC2 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=0 -> n=0 -> m=0 -> k+1 < 2^lenL)
| cfgL2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) 
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
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i (lenL+1)).
      rw_pa.
      spl.
    + eex cfgR.
      1: apply LC_Inc; lia.
      lia.
  - eex cfgL.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR1.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC1_Ov_0; lia.
        spl.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eex cfgR2.
        1: apply RC1_Ov; lia.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + eex cfgL1.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eex cfgR2.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eex cfgR.
        1: apply RC2_Ov_0; lia.
        spl.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eex cfgR2.
        1: apply RC2_Ov; lia.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + eex cfgL2.
      1: apply RC2_Inc; lia.
      lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 203 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM254.


Module TM246.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RE_1LB0LD_1RF0RA_1RB---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv_0 r n:
  halts tm (ldh <* ld1^^(2+n) <| rd0 *> r).
Proof.
  esx.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1^^(n*2+1) |> [0] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i*2+1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2+1) |> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2))*2) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2))*2) |> RC 0.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL /\ k mod 2 <> n mod 2
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + divmod2_cases n.
      1: lia.
      lowbit_cases n'.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      spl.
      pose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM246.


Module TM247.
Definition tm := Eval compute in (TM_from_str "1RB1LF_1RC1LB_1LD1RE_1LB0LD_1RA0RA_0RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv_0 r n:
  halts tm (ldh <* ld1^^(2+n) <| rd0 *> r).
Proof.
  esx.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1^^(n*2+1) |> [0] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i*2+1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2+1) |> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2))*2) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2))*2) |> RC 0.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL /\ k mod 2 <> n mod 2
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + divmod2_cases n.
      1: lia.
      lowbit_cases n'.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      spl.
      pose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM247.


Module TM244.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1RF_0LC1LC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;0;1] {{A}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;1;1;0;1] {{E}}> r) (at level 30).
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(1+n) <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_0_0 l r:
  l <* ld0 |2> rd0 *> r -->+
  l |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0_1 l r:
  l <* ld1 |2> rd0 *> r -->+
  l |1> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2+2) |2> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2+3) |2> r.
Proof.
  es.
Qed.

Lemma ROv21 l r n:
  l |1> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2+3) |2> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC2 lenR (1+n) m -->+
  l <1| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL r:
  LC lenL O <| r -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |2> r.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1 lenL n i:
  LC lenL O <1| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC'_1 lenL k n:
  k<2^lenL ->
  LC lenL k |2> RC (n*2+1) -->+
  LC (lenL+1+1) ((k*2)*2+1) |2> RC n.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_0_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k |> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_0_0.
Qed.

Lemma RC'_0_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (0*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_0_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_0_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_0_1.
Qed.

Lemma RC'_0_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (0*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_0_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+2)) (((k*2+1)*2+1)*2^(lenR*2+2)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+3)) (((k*2+1)*2+1)*2^(lenR*2+3)-1) |2> RC m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+3)) (((k*2)*2+1)*2^(lenR*2+3)-1) |2> RC m.
Proof.
  solve_rule ROv21.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgLx(lenL k n:nat)
| cfgR3(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR2x(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgLx lenL k n => LC lenL k <1| RC n
| cfgR3 lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR2x lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgLx lenL k n => 1 <= k+n < 2^lenL
| cfgR3 lenL k n => n*4 < k < 2^lenL /\
  (n=O -> k+2<2^lenL)
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + eex cfgR3.
      1: apply LC_Ov.
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgLx.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - divmod2_cases n.
    + remember (lenL-1) as lenL'.
      assert (HlenL:lenL<>O) by (intro; subst; lia).
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases k.
      * lowbit_cases n'.
        {
          rw_pa.
          eex cfgLx.
          1: follow10 RC'_0_1_0; follow100 RC_Inc1; finish.
          spl.
        }
        {
          rw_pa.
          eex cfgR2x.
          1: apply RC'_0_1; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'.
        {
          rw_pa.
          eex cfgL.
          1: follow10 RC'_0_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          rw_pa.
          eex cfgR2.
          1: apply RC'_0_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
    + eex cfgR3.
      1: apply RC'_1; lia.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC2_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2x.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC2_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 10 607 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM244.


Module TM234.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1RD0RA_1RE---_1RF1LF_1LB1RC").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;0;1] {{F}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{C}} [0;1;1;1;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;0;1;1;1] {{F}}> r) (at level 30).

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^(n+1) |1> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(n+1) <* ld1 |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv11 l r n:
  l |1> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv21 l r n:
  l |1> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) <* ld0 |> [0] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma RC2_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC2 lenR (1+n) m -->+
  l <1| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov_0 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_1.
Qed.

Lemma LC_Ov1 lenL x i:
  LC lenL 0 <1| RC ((x*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv11.
Qed.

Lemma RC1_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv11 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv21.
Qed.

Lemma RC2_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv21 _ 0inf _) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgLx(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1x(lenL k lenR n m:nat)
| cfgR2x(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgLx lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1x lenL k lenR n m => LC lenL k |1> RC1 lenR n m
| cfgR2x lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgLx lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eex cfgR2x.
        1: apply LC_Ov_0.
        pose proof (split_bound_v1 x i lenL).
        spl.
      * lowbit_cases n'.
        1: lia.
        eex cfgR1x.
        1: apply LC_Ov_1.
        pose proof (split_bound_v1 x i lenL).
        spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgLx.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1x.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2x.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC2_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC2_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 53 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM234.


Module TM235.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RF_1RE---_1RA0RF_1LB1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;0;1] {{A}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{C}} [0;1;1;1;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;0;1;1;1] {{A}}> r) (at level 30).

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^(n+1) |1> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(n+1) <* ld1 |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv11 l r n:
  l |1> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv21 l r n:
  l |1> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) <* ld0 |> [0] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma RC2_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC2 lenR (1+n) m -->+
  l <1| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov_0 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_1.
Qed.

Lemma LC_Ov1 lenL x i:
  LC lenL 0 <1| RC ((x*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv11.
Qed.

Lemma RC1_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv11 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv21.
Qed.

Lemma RC2_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv21 _ 0inf _) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgLx(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1x(lenL k lenR n m:nat)
| cfgR2x(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgLx lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1x lenL k lenR n m => LC lenL k |1> RC1 lenR n m
| cfgR2x lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgLx lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eex cfgR2x.
        1: apply LC_Ov_0.
        pose proof (split_bound_v1 x i lenL).
        spl.
      * lowbit_cases n'.
        1: lia.
        eex cfgR1x.
        1: apply LC_Ov_1.
        pose proof (split_bound_v1 x i lenL).
        spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgLx.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1x.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2x.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC2_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC2_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 53 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM235.


Module TM236.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA0RF_1LB1RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1;0;1] {{A}}> r) (at level 30).


Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{C}} [0;1;1;1;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;0;1;1;1] {{A}}> r) (at level 30).

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^(n+1) |1> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(n+1) <* ld1 |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv11 l r n:
  l |1> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv21 l r n:
  l |1> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2) <* ld0 |> [0] *> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma RC2_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC2 lenR (1+n) m -->+
  l <1| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov_0 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv_1.
Qed.

Lemma LC_Ov1 lenL x i:
  LC lenL 0 <1| RC ((x*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2+1)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv11.
Qed.

Lemma RC1_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2) (((k*2)*2+1)*2^(lenR*2)-1) |> RC 0.
Proof.
  epose proof (ROv11 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv21.
Qed.

Lemma RC2_Ov1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 0 -->+
  LC (lenL+1+1+lenR*2+1) ((((k*2)*2+1)*2^(lenR*2)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv21 _ 0inf _) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgLx(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1x(lenL k lenR n m:nat)
| cfgR2x(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgLx lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1x lenL k lenR n m => LC lenL k |1> RC1 lenR n m
| cfgR2x lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgLx lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eex cfgR2x.
        1: apply LC_Ov_0.
        pose proof (split_bound_v1 x i lenL).
        spl.
      * lowbit_cases n'.
        1: lia.
        eex cfgR1x.
        1: apply LC_Ov_1.
        pose proof (split_bound_v1 x i lenL).
        spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgLx.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1x.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC1_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2x.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC2_Ov1_0; follow100 RC_Inc; finish.
      spl.
      solve_v1 k lenL (lenR*2).
    + eex cfgR1.
      1: apply RC2_Ov1; lia.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 53 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM236.


Module TM237.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD1RF_1RE---_1RA0RA_0LE1LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;0;1] {{A}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;1;1] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma RInc1 l r n:
  l |1> rd1^^n *> [0] *> r -->+
  l <1| rd0^^n *> [1] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;1;1;0;1] {{E}}> r) (at level 30).
Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(1+n) <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_0_0 l r:
  l <* ld0 |2> rd0 *> r -->+
  l |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0_1 l r:
  l <* ld1 |2> rd0 *> r -->+
  l |1> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2+2) |2> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2+3) |2> r.
Proof.
  es.
Qed.

Lemma ROv21 l r n:
  l |1> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld1 <* ld0^^(n*2+3) |2> r.
Proof.
  es.
Qed.

Lemma LC_Inc len n r:
  1+n<2^len ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc.
Qed.

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc n l:
  l |> RC n -->+
  l <| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC1 lenR (1+n) m -->+
  l <| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc l lenR n m:
  1+n<2^(lenR+1) ->
  l |> RC2 lenR (1+n) m -->+
  l <| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC2 lenR (1+n) m -->+
  l <1| RC2 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL r:
  LC lenL O <| r -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |2> r.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1 lenL n i:
  LC lenL O <1| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC'_1 lenL k n:
  k<2^lenL ->
  LC lenL k |2> RC (n*2+1) -->+
  LC (lenL+1+1) ((k*2)*2+1) |2> RC n.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_0_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k |> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_0_0.
Qed.

Lemma RC'_0_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (0*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_0_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_0_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_0_1.
Qed.

Lemma RC'_0_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (0*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_0_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+2)) (((k*2+1)*2+1)*2^(lenR*2+2)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+3)) (((k*2+1)*2+1)*2^(lenR*2+3)-1) |2> RC m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 m -->+
  LC (lenL+1+1+(lenR*2+3)) (((k*2)*2+1)*2^(lenR*2+3)-1) |2> RC m.
Proof.
  solve_rule ROv21.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgLx(lenL k n:nat)
| cfgR3(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR2x(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgLx lenL k n => LC lenL k <1| RC n
| cfgR3 lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR2x lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgLx lenL k n => 1 <= k+n < 2^lenL
| cfgR3 lenL k n => n*4 < k < 2^lenL /\
  (n=O -> k+2<2^lenL)
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2x lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + eex cfgR3.
      1: apply LC_Ov.
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgLx.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - divmod2_cases n.
    + remember (lenL-1) as lenL'.
      assert (HlenL:lenL<>O) by (intro; subst; lia).
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases k.
      * lowbit_cases n'.
        {
          rw_pa.
          eex cfgLx.
          1: follow10 RC'_0_1_0; follow100 RC_Inc1; finish.
          spl.
        }
        {
          rw_pa.
          eex cfgR2x.
          1: apply RC'_0_1; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'.
        {
          rw_pa.
          eex cfgL.
          1: follow10 RC'_0_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          rw_pa.
          eex cfgR2.
          1: apply RC'_0_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
    + eex cfgR3.
      1: apply RC'_1; lia.
      spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC2_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2x.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR3.
    1: apply RC2_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL (lenR*2+2).
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 10 607 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM237.


