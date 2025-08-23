From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import ES_v2.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

Notation ld0 := <[0;0;1].
Notation ld1 := <[1;1;1].
Notation ldh := (const 0 <* <[1;1;1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].


Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> BinInc rd1 m). 
Definition RC2 len n m := BinDec2 [0] [1] [0;0] len n ([0] *> rd1 *> BinInc rd1 m). 

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


Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Ltac spl := repeat split; try lia; try solve[solve_pow2_lt].

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  rw_pa.

Ltac eex f :=
  (eexists (f _ _ _ _ _) ||
  eexists (f _ _ _ _) ||
  eexists (f _ _ _)); split.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_1RD0LC_0LE1LD_1RA0RB_0RD0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;0] {{B}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;0;0] {{D}}> r) (at level 30).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv2 l r n:
  l |> rd1^^n *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^n <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r n:
  l <* ld0 <* ld1^^n |2> rd1 *> r -->+
  l <* ld1 <* ld0^^(1+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l |> [0;0] *> r.
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

Lemma RC2_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC2 len (1+n) m -->+
  l <| RC2 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov lenL r:
  LC lenL 0 <| r -->+
  LC (lenL+1) ((2^lenL-1)*2) |2> r.
Proof.
  solve_rule LOv.
Qed.

Lemma RC2_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 m -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2) |2> RC m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC'_1 lenL k m:
  k+1<2^lenL ->
  LC lenL (k+1) |2> RC (m*2+1) -->+
  LC (lenL+1) (k*2+1) |2> RC m.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add by lia.
  epose proof (lowbit_split x i lenL).
  epose proof (lowbit_split_lt x i lenL).
  rewrite H0 by lia.
  unfold LC,RC.
  rw_Bin.
  all: solve_pow2_lt.
  solve_rule ROv'_1.
Qed.

Lemma RC'_0 l x i:
  l |2> RC ((x*2+1)*2^i*2) -->+
  l |> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_0.
Qed.

Lemma RC'_0_0 l:
  l |2> RC (0*2) -->+
  l |> RC 0.
Proof.
  unfold RC.
  es.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR'(lenL k n:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR' lenL k n => LC lenL k |2> RC n
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k+n < 2^lenL
| cfgR2 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR' lenL k n => n <= k < 2^lenL /\
  (n=O -> k+1<2^lenL)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + eex cfgR'.
      1: apply LC_Ov.
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC2_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros.
      subst.
      solve_v1 k lenL lenR.
  - divmod2_cases n.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC'_0_0; follow100 RC_Inc; finish.
        lia.
      * eex cfgR2.
        1: apply RC'_0.
        epose proof (split_bound_v2 x i).
        spl.
    + replace k with (k-1+1) by lia.
      eex cfgR'.
      1: apply RC'_1; lia.
      spl.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 3 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM1.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_0LD1LC_1RE0RA_1RA---_0RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0] {{A}}> r) (at level 30).

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

Notation "l <1| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [0;0] {{A}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> rd1 *> r.
Proof.
  es.
Qed.

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^(1+n) |1> [0;0] *> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv12 l r n:
  l |1> rd1^^n *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^n |1> [0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r k n m:
  l <* ld0 <* ld1^^k |> rd1^^n *> [1;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n+k) |1> [0;0] *> rd0^^m *> rd1 *> r.
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

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc1 len n m l:
  1+n<2^(len+1) ->
  l |1> RC2 len (1+n) m -->+
  l <1| RC2 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n:
  LC lenL O <| RC n -->+
  LC lenL (2^lenL-1) |1> RC (n*2+1).
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2+1) -->+
  LC (1+lenL) (2^(1+lenL)-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_1_0 lenL:
  LC lenL O <1| RC (0*2+1) -->+
  LC (1+lenL) (2^(1+lenL)-1) |1> RC 0.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (1+lenL) (2^(1+lenL)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (1+lenL) (2^(1+lenL)-1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv12.
Qed.

Lemma RC2_Ov1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv12 _ 0inf _) as I1.
  unfold LC,RC2,RC.
  intros.
  rw_Bin.
  all: solve_pow2_lt.
  follow10 I1.
  simpl_tape.
  finish.
Qed.

Lemma RC1_Ov lenL k lenR i2 x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR+i2)) ((k*2+1)*2^(1+lenR+i2)-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
| cfgL' lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL*4 /\ k+n <> 2^lenL*2
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgL'.
      1: follow10 LC_Ov; follow100 RC_Inc1; finish.
      spl.
      pp_pow2_lt_le i lenL.
      remember (lenL-1-i) as lenL'.
      replace lenL with (lenL'+1+i) in * by lia.
      rw_pa; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eex cfgR1.
        1: apply LC_Ov1_0.
        spl.
        unshelve epose proof (split_bound_v1 x (i+1) (lenL+2) _) as I1.
        1: rw_pa; lia.
        pp_pow2_lt_le i lenL.
        destruct x.
        {
          assert (i<lenL\/i=lenL) as [E|E] by lia.
          1: lia.
          subst; lia.
        }
        zify_le_mul_r; lia.
      * lowbit_cases n'.
        {
          eex cfgL'.
          1: follow10 LC_Ov1_1_0; follow100 RC_Inc1; finish.
          spl.
        }
        {
          eex cfgR2.
          1: apply LC_Ov1_1; lia.
          spl.
          epose proof (split_bound_v1 x (i) (lenL+1)).
          rw_pa; lia.
        }
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - destruct n.
    2:{
      destruct k.
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    lowbit_cases k.
    1: lia.
    epose proof (lowbit_split x0 i0 lenL) as I1.
    epose proof (lowbit_split_lt x0 i0 lenL) as I2.
    remember (lenL-1-i0) as lenL'.
    replace lenL with (lenL'+1+i0) in * by lia.
    clear HeqlenL'.
    eex cfgR2.
    1: apply RC1_Ov.
    1: applys_eq I2; f_equal; lia.
    clear I1 I2.
    rewrite (Nat.add_comm (1+lenR) i0).
    spl.
    + rw_pa.
      repeat rewrite Nat.mul_assoc.
      epose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
    + rw_pa.
      repeat rewrite Nat.mul_assoc.
      epose proof (Nat.mul_le_mono_pos_r (x0*2+1) (2^(lenL'+1)) (2^i0)).
      epose proof (Nat.mul_le_mono_pos_r (x0*2+1) (2^(lenL'+1)) (2^(i0+lenR))).
      rw_pa; lia.
  - destruct n.
    2:{
      destruct k.
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL'.
      1: follow10 RC2_Ov1_0; follow100 RC_Inc1; finish.
      spl.
      * solve_v1 k lenL lenR.
      * solve_v1 k lenL lenR.
    + eex cfgR2.
      1: apply RC2_Ov1; lia.
      spl.
      epose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL' 4 5 3)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_1LD0LC_0LE1LD_1RA0RB_0RD0RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0] {{B}}> r) (at level 30).

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

Notation "l <1| r" := (l <{{E}} [0;1] *> r) (at level 30).
Notation "l |1> r" := (l <* [0;0] {{B}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> rd1 *> r.
Proof.
  es.
Qed.

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^(1+n) |1> [0;0] *> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv12 l r n:
  l |1> rd1^^n *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^n |1> [0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1 l r k n m:
  l <* ld0 <* ld1^^k |> rd1^^n *> [1;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n+k) |1> [0;0] *> rd0^^m *> rd1 *> r.
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

Lemma LC_Inc1 len n r:
  1+n<2^len ->
  LC len (1+n) <1| r -->+
  LC len n |1> r.
Proof.
  intros H.
  apply LBinDec_spec; try lia.
  follow' LInc1.
Qed.

Lemma RC_Inc1 n l:
  l |1> RC n -->+
  l <1| RC (1+n).
Proof.
  apply RBinInc_spec.
  follow' RInc1.
Qed.

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC2_Inc1 len n m l:
  1+n<2^(len+1) ->
  l |1> RC2 len (1+n) m -->+
  l <1| RC2 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n:
  LC lenL O <| RC n -->+
  LC lenL (2^lenL-1) |1> RC (n*2+1).
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2+1) -->+
  LC (1+lenL) (2^(1+lenL)-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_1_0 lenL:
  LC lenL O <1| RC (0*2+1) -->+
  LC (1+lenL) (2^(1+lenL)-1) |1> RC 0.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (1+lenL) (2^(1+lenL)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (1+lenL) (2^(1+lenL)-1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv12.
Qed.

Lemma RC2_Ov1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |1> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv12 _ 0inf _) as I1.
  unfold LC,RC2,RC.
  intros.
  rw_Bin.
  all: solve_pow2_lt.
  follow10 I1.
  simpl_tape.
  finish.
Qed.

Lemma RC1_Ov lenL k lenR i2 x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR+i2)) ((k*2+1)*2^(1+lenR+i2)-1) |1> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |1> RC2 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
| cfgL' lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL*4 /\ k+n <> 2^lenL*2
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgL'.
      1: follow10 LC_Ov; follow100 RC_Inc1; finish.
      spl.
      pp_pow2_lt_le i lenL.
      remember (lenL-1-i) as lenL'.
      replace lenL with (lenL'+1+i) in * by lia.
      rw_pa; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eex cfgR1.
        1: apply LC_Ov1_0.
        spl.
        unshelve epose proof (split_bound_v1 x (i+1) (lenL+2) _) as I1.
        1: rw_pa; lia.
        pp_pow2_lt_le i lenL.
        destruct x.
        {
          assert (i<lenL\/i=lenL) as [E|E] by lia.
          1: lia.
          subst; lia.
        }
        zify_le_mul_r; lia.
      * lowbit_cases n'.
        {
          eex cfgL'.
          1: follow10 LC_Ov1_1_0; follow100 RC_Inc1; finish.
          spl.
        }
        {
          eex cfgR2.
          1: apply LC_Ov1_1; lia.
          spl.
          epose proof (split_bound_v1 x (i) (lenL+1)).
          rw_pa; lia.
        }
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
  - destruct n.
    2:{
      destruct k.
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    lowbit_cases k.
    1: lia.
    epose proof (lowbit_split x0 i0 lenL) as I1.
    epose proof (lowbit_split_lt x0 i0 lenL) as I2.
    remember (lenL-1-i0) as lenL'.
    replace lenL with (lenL'+1+i0) in * by lia.
    clear HeqlenL'.
    eex cfgR2.
    1: apply RC1_Ov.
    1: applys_eq I2; f_equal; lia.
    clear I1 I2.
    rewrite (Nat.add_comm (1+lenR) i0).
    spl.
    + rw_pa.
      repeat rewrite Nat.mul_assoc.
      epose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
    + rw_pa.
      repeat rewrite Nat.mul_assoc.
      epose proof (Nat.mul_le_mono_pos_r (x0*2+1) (2^(lenL'+1)) (2^i0)).
      epose proof (Nat.mul_le_mono_pos_r (x0*2+1) (2^(lenL'+1)) (2^(i0+lenR))).
      rw_pa; lia.
  - destruct n.
    2:{
      destruct k.
      1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL'.
      1: follow10 RC2_Ov1_0; follow100 RC_Inc1; finish.
      spl.
      * solve_v1 k lenL lenR.
      * solve_v1 k lenL lenR.
    + eex cfgR2.
      1: apply RC2_Ov1; lia.
      spl.
      epose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL' 4 5 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM3.


