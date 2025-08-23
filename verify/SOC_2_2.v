From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat.
Require Import Lia PeanoNat String.
From BusyCoq Require Import ES_v2.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0].
Notation rd1 := [1;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0] len n (rd1 *> BinInc rd1 m). 
Definition RC2 len n m := BinDec2 [0] [1] [0] len n ([0] *> rd1 *> BinInc rd1 m). 

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


Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1LB1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1;1] {{F}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;0;1] {{F}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> [0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;0;1] {{C}}> r) (at level 30).

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^n <* ld0 <* ld1 <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |1> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_00_0 l r:
  l <* ld0 |2> rd0 *> rd0 *> r -->+
  l |1> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00_1 l r:
  l <* ld1 |2> rd0 *> rd0 *> r -->+
  l |> [0] *> r.
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

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |1> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL n:
  LC lenL O <1| RC (n*2+1) -->+
  LC (lenL+1+1+1+1) (((2^lenL-1)*2+1)*2*2*2+1) |2> RC n.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) ((k*2*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) (((k*2+1)*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC'_1 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC (m*2+1) -->+
  LC (lenL+1) (k*2) |2> RC m.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_0.
Qed.

Lemma RC'_00_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((0*2)*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_00_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_00_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_1.
Qed.

Lemma RC'_00_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((0*2)*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_00_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgL' lenL k n => 1 <= k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\
  (m=O -> k+2<2^lenL) /\
  (m=1 -> k+1<2^lenL)
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgR1'.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov1_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply LC_Ov1_0.
          pose proof (split_bound_v1 x i lenL).
          spl.
        }
      * eex cfgR'.
        1: apply LC_Ov1_1.
        spl.
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      lia.
  - divmod2_cases n.
    + divmod2_cases n'.
      * destruct lenL.
        1: lia.
        replace (S lenL) with (lenL+1) in * by lia.
        divmod2_cases k.
        {
          lowbit_cases n'0.
          {
            eex cfgL.
            1: follow10 RC'_00_1_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1.
            1: apply RC'_00_1; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
        {
          lowbit_cases n'0.
          {
            eex cfgL'.
            1: follow10 RC'_00_0_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc1; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1'.
            1: apply RC'_00_0; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + eex cfgR'.
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
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 151 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM7.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1RD0RF_1RE---_1RA1LF_1LB1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1;1] {{A}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;0;1] {{A}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> [0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;0;1] {{C}}> r) (at level 30).

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^n <* ld0 <* ld1 <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |1> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_00_0 l r:
  l <* ld0 |2> rd0 *> rd0 *> r -->+
  l |1> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00_1 l r:
  l <* ld1 |2> rd0 *> rd0 *> r -->+
  l |> [0] *> r.
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

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |1> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL n:
  LC lenL O <1| RC (n*2+1) -->+
  LC (lenL+1+1+1+1) (((2^lenL-1)*2+1)*2*2*2+1) |2> RC n.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) ((k*2*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) (((k*2+1)*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC'_1 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC (m*2+1) -->+
  LC (lenL+1) (k*2) |2> RC m.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_0.
Qed.

Lemma RC'_00_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((0*2)*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_00_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_00_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_1.
Qed.

Lemma RC'_00_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((0*2)*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_00_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgL' lenL k n => 1 <= k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\
  (m=O -> k+2<2^lenL) /\
  (m=1 -> k+1<2^lenL)
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgR1'.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov1_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply LC_Ov1_0.
          pose proof (split_bound_v1 x i lenL).
          spl.
        }
      * eex cfgR'.
        1: apply LC_Ov1_1.
        spl.
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      lia.
  - divmod2_cases n.
    + divmod2_cases n'.
      * destruct lenL.
        1: lia.
        replace (S lenL) with (lenL+1) in * by lia.
        divmod2_cases k.
        {
          lowbit_cases n'0.
          {
            eex cfgL.
            1: follow10 RC'_00_1_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1.
            1: apply RC'_00_1; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
        {
          lowbit_cases n'0.
          {
            eex cfgL'.
            1: follow10 RC'_00_0_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc1; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1'.
            1: apply RC'_00_0; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + eex cfgR'.
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
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 151 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM2.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_0RD0RF_1LE---_1RA1LF_1LB1RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1;1] {{A}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;0;1] {{A}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> [0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;0;1] {{C}}> r) (at level 30).

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^n <* ld0 <* ld1 <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |1> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_00_0 l r:
  l <* ld0 |2> rd0 *> rd0 *> r -->+
  l |1> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00_1 l r:
  l <* ld1 |2> rd0 *> rd0 *> r -->+
  l |> [0] *> r.
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

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |1> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL n:
  LC lenL O <1| RC (n*2+1) -->+
  LC (lenL+1+1+1+1) (((2^lenL-1)*2+1)*2*2*2+1) |2> RC n.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) ((k*2*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) (((k*2+1)*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC'_1 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC (m*2+1) -->+
  LC (lenL+1) (k*2) |2> RC m.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_0.
Qed.

Lemma RC'_00_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((0*2)*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_00_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_00_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_1.
Qed.

Lemma RC'_00_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((0*2)*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_00_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgL' lenL k n => 1 <= k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\
  (m=O -> k+2<2^lenL) /\
  (m=1 -> k+1<2^lenL)
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgR1'.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov1_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply LC_Ov1_0.
          pose proof (split_bound_v1 x i lenL).
          spl.
        }
      * eex cfgR'.
        1: apply LC_Ov1_1.
        spl.
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      lia.
  - divmod2_cases n.
    + divmod2_cases n'.
      * destruct lenL.
        1: lia.
        replace (S lenL) with (lenL+1) in * by lia.
        divmod2_cases k.
        {
          lowbit_cases n'0.
          {
            eex cfgL.
            1: follow10 RC'_00_1_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1.
            1: apply RC'_00_1; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
        {
          lowbit_cases n'0.
          {
            eex cfgL'.
            1: follow10 RC'_00_0_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc1; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1'.
            1: apply RC'_00_0; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + eex cfgR'.
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
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 151 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM3.


Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_0RD0RA_1LE---_1RF0RA_1LB1RE").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;1;1;1;0;0;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1;1] {{F}}> r) (at level 30).

Notation "l <1| r" := (l <{{C}} [0;1;1;1;1;0;0;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;1;1;1;0;1;0;1] {{F}}> r) (at level 30).

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

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |1> [0] *> r.
Proof.
  es.
Qed.

Notation "l |2> r" := (l <* [1;0;1] {{C}}> r) (at level 30).

Lemma LOv1_1 r n:
  ldh <* ld1^^n <1| rd1 *> r -->+
  ldh <* ld0^^n <* ld0 <* ld1 <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma LOv1_0 r n:
  ldh <* ld1^^n <1| rd0 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv1 l r n:
  l |1> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(2+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_00_0 l r:
  l <* ld0 |2> rd0 *> rd0 *> r -->+
  l |1> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00_1 l r:
  l <* ld1 |2> rd0 *> rd0 *> r -->+
  l |> [0] *> r.
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

Lemma RC1_Inc1 l lenR n m:
  1+n<2^(lenR+1) ->
  l |1> RC1 lenR (1+n) m -->+
  l <1| RC1 lenR n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc1.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |1> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1_1 lenL n:
  LC lenL O <1| RC (n*2+1) -->+
  LC (lenL+1+1+1+1) (((2^lenL-1)*2+1)*2*2*2+1) |2> RC n.
Proof.
  solve_rule LOv1_1.
Qed.

Lemma LC_Ov1_0 lenL x i:
  LC lenL O <1| RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule LOv1_0.
Qed.

Lemma LC_Ov1_0_0 lenL:
  LC lenL O <1| RC (0*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC 0.
Proof.
  epose proof (LOv1_0 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) ((k*2*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |1> RC1 lenR 0 m -->+
  LC (lenL+1+1+(2+lenR)) (((k*2+1)*2+1)*2^(2+lenR)-1) |2> RC m.
Proof.
  solve_rule ROv1.
Qed.

Lemma RC'_1 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC (m*2+1) -->+
  LC (lenL+1) (k*2) |2> RC m.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00_0 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_0.
Qed.

Lemma RC'_00_0_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2+1) |2> RC ((0*2)*2) -->+
  LC lenL k |1> RC 0.
Proof.
  epose proof (ROv'_00_0 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_00_1 lenL k x i:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC lenL k |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00_1.
Qed.

Lemma RC'_00_1_0 lenL k:
  k<2^lenL ->
  LC (lenL+1) (k*2) |2> RC ((0*2)*2) -->+
  LC lenL k |> RC 0.
Proof.
  epose proof (ROv'_00_1 _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL
| cfgL' lenL k n => 1 <= k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\
  (m=O -> k+2<2^lenL) /\
  (m=1 -> k+1<2^lenL)
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1' lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
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
      eex cfgR1'.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov1_0_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply LC_Ov1_0.
          pose proof (split_bound_v1 x i lenL).
          spl.
        }
      * eex cfgR'.
        1: apply LC_Ov1_1.
        spl.
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      lia.
  - divmod2_cases n.
    + divmod2_cases n'.
      * destruct lenL.
        1: lia.
        replace (S lenL) with (lenL+1) in * by lia.
        divmod2_cases k.
        {
          lowbit_cases n'0.
          {
            eex cfgL.
            1: follow10 RC'_00_1_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1.
            1: apply RC'_00_1; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
        {
          lowbit_cases n'0.
          {
            eex cfgL'.
            1: follow10 RC'_00_0_0.
            1: rw_pa; lia.
            1: follow100 RC_Inc1; finish.
            rw_pa.
            spl.
          }
          {
            eex cfgR1'.
            1: apply RC'_00_0; rw_pa; lia.
            rw_pa.
            pose proof (split_bound_v2 x i).
            spl.
          }
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + eex cfgR'.
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
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov1; lia.
    spl.
    + zify_le_mul_r; lia.
    + intros; subst.
      solve_v1 k lenL lenR.
    + intros; subst.
      solve_v1 k lenL lenR.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 151 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM4.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RA_1RD0LC_1LE---_1RF1LE_1RC1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{B}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [1;0;1] {{C}}> r) (at level 30).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(1+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <| [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00 l r:
  l |2> rd0 *> rd0 *> r -->+
  l <* ld1 |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n) |2> r.
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

Lemma LC_Ov lenL r:
  LC lenL 0 <| r-->+
  LC (lenL+1) ((2^lenL-1)*2+1) |2> r.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+lenR+1) ((k*2+1)*2^lenR*2) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC (lenL+1) (k*2) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00.
Qed.

Lemma RC'_00_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC ((0*2)*2) -->+
  LC (lenL+1) (k*2) |> RC 0.
Proof.
  epose proof (ROv'_00 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_1 l x i:
  l |2> RC (((x*2+1)*2^i)*2+1) -->+
  l <| RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_1_0 l:
  l |2> RC (0*2+1) -->+
  l <| RC 0.
Proof.
  solve_rule ROv'_1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
  - divmod2_cases n.
    + divmod2_cases n'.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC'_00_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply RC'_00; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + lowbit_cases n'.
      * eex cfgL.
        1: apply RC'_1_0; lia.
        spl.
      * destruct k.
        1: lia.
        eex cfgR1.
        1: follow10 RC'_1; follow100 LC_Inc; finish.
        epose proof (split_bound_v2 x i).
        spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM1.


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1RC0LB_1LD---_1RE1LD_1LB1RF_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;0;1] {{E}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [1;0;1] {{B}}> r) (at level 30).

Lemma LOv r n:
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(1+n) |2> r.
Proof.
  es.
Qed.

Lemma ROv'_01 l r:
  l |2> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 |2> r.
Proof.
  es.
Qed.

Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <| [0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_00 l r:
  l |2> rd0 *> rd0 *> r -->+
  l <* ld1 |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n) |2> r.
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

Lemma LC_Ov lenL r:
  LC lenL 0 <| r-->+
  LC (lenL+1) ((2^lenL-1)*2+1) |2> r.
Proof.
  solve_rule LOv.
Qed.

Lemma RC1_Ov lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 m -->+
  LC (lenL+1+lenR+1) ((k*2+1)*2^lenR*2) |2> RC m.
Proof.
  solve_rule ROv.
Qed.

Lemma RC'_01 lenL k m:
  k<2^lenL ->
  LC lenL k |2> RC ((m*2+1)*2) -->+
  LC (lenL+1+1) (k*2*2+1) |2> RC m.
Proof.
  solve_rule ROv'_01.
Qed.

Lemma RC'_00 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i*2)*2) -->+
  LC (lenL+1) (k*2) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_00.
Qed.

Lemma RC'_00_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC ((0*2)*2) -->+
  LC (lenL+1) (k*2) |> RC 0.
Proof.
  epose proof (ROv'_00 _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC'_1 l x i:
  l |2> RC (((x*2+1)*2^i)*2+1) -->+
  l <| RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv'_1.
Qed.

Lemma RC'_1_0 l:
  l |2> RC (0*2+1) -->+
  l <| RC 0.
Proof.
  solve_rule ROv'_1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR' lenL k n => LC lenL k |2> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k+n < 2^lenL
| cfgR' lenL k m => m < k < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
  - divmod2_cases n.
    + divmod2_cases n'.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC'_00_0; follow100 RC_Inc; finish.
          spl.
        }
        {
          eex cfgR1.
          1: apply RC'_00; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * eex cfgR'.
        1: apply RC'_01; lia.
        spl.
    + lowbit_cases n'.
      * eex cfgL.
        1: apply RC'_1_0; lia.
        spl.
      * destruct k.
        1: lia.
        eex cfgR1.
        1: follow10 RC'_1; follow100 LC_Inc; finish.
        epose proof (split_bound_v2 x i).
        spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgR'.
    1: apply RC1_Ov; lia.
    spl.
    zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM5.


