From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
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

Module TM146.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_0RF0LD_1RC---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld0 <* ld1^^(n*3+2) |> [0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [0] *> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> rd0 *> r.
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

Lemma RC1_Ov_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC2 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)) |> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)) |> RC 0.
Proof.
  epose proof (ROv2_0_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+(lenR*3+1)) ((k*2+1)*2^(lenR*3+1)-1) |> RC1 (i+1) (((2^i-1)*2+1)*2+1) x.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_0_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2+1) -->+
  LC (lenL+1+(lenR*3+1)) ((k*2+1)*2^(lenR*3+1)-1) |> RC 0.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+(lenR*3+4)) ((k*2+1)*2^(lenR*3+4)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv2_1_0.
Qed.

Lemma RC2_Ov_1_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (0*2) -->+
  LC (lenL+1+(lenR*3+4)) ((k*2+1)*2^(lenR*3+4)-1) |> RC 0.
Proof.
  epose proof (ROv2_1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_1_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC2 (i+1) (((2^i-1)*2+1)*2) x.
Proof.
  solve_rule ROv2_1_1.
Qed.

Lemma RC2_Ov_1_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (0*2+1) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC 1.
Proof.
  solve_rule ROv2_1_1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1 <> 2^lenL)
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
      spl.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        rw_pa.
        spl.
        destruct n'.
        1: lia.
        replace (S n'*3) with (n'*3+3) by lia.
        solve_v1 k lenL (n'*3).
      * eex cfgR2.
        1: apply RC1_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc; finish.
        solve_v1 k lenL (n'*3).
      * eex cfgR1.
        1: apply RC1_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_0_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_0_1; lia.
          spl.
          pose proof (split_bound_v2 x i).
          zify_le_mul_r; lia.
        }
    + divmod2_cases m.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_1_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_1_1; lia.
          spl.
          pose proof (split_bound_v2 x i).
          zify_le_mul_r; lia.
        }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 9 271 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM146.


Module TM147.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_1RB---").
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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_0 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld0 <* ld1^^(n*3+2) |> [0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_1 l r n:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [0] *> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_0 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> rd0 *> r.
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

Lemma RC1_Ov_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC2 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)) |> RC2 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)) |> RC 0.
Proof.
  epose proof (ROv2_0_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+(lenR*3+1)) ((k*2+1)*2^(lenR*3+1)-1) |> RC1 (i+1) (((2^i-1)*2+1)*2+1) x.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_0_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2+1) -->+
  LC (lenL+1+(lenR*3+1)) ((k*2+1)*2^(lenR*3+1)-1) |> RC 0.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+(lenR*3+4)) ((k*2+1)*2^(lenR*3+4)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv2_1_0.
Qed.

Lemma RC2_Ov_1_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (0*2) -->+
  LC (lenL+1+(lenR*3+4)) ((k*2+1)*2^(lenR*3+4)-1) |> RC 0.
Proof.
  epose proof (ROv2_1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_1_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC2 (i+1) (((2^i-1)*2+1)*2) x.
Proof.
  solve_rule ROv2_1_1.
Qed.

Lemma RC2_Ov_1_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (0*2+1) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC 1.
Proof.
  solve_rule ROv2_1_1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1 <> 2^lenL)
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
      spl.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        rw_pa.
        spl.
        destruct n'.
        1: lia.
        replace (S n'*3) with (n'*3+3) by lia.
        solve_v1 k lenL (n'*3).
      * eex cfgR2.
        1: apply RC1_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc; finish.
        solve_v1 k lenL (n'*3).
      * eex cfgR1.
        1: apply RC1_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_0_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_0_1; lia.
          spl.
          pose proof (split_bound_v2 x i).
          zify_le_mul_r; lia.
        }
    + divmod2_cases m.
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_1_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases n'0.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_1_1; lia.
          spl.
          pose proof (split_bound_v2 x i).
          zify_le_mul_r; lia.
        }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM147.


Module TM39.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{B}}> r) (at level 30).

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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m*3+n*3+2) |> [1;0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_0_1 l r n m:
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m*3+n*3+4) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_0 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m*3+n*3+4) |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv2_1_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m*3+n*3+5) |> [1;0] *> r.
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

Lemma RC1_Ov_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC2 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*3+2)) ((k*2+1)*2^(lenR*3+2)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_0 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (((x*2+1)*2^i0*2+1)*2^(i*2)-1) -->+
  LC (lenL+1+(i*3+lenR*3+2)) ((k*2+1)*2^(i*3+lenR*3+2)-1) |> RC2 i0 ((2^i0-1)*2) x.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_0_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((0*2+1)*2^(i*2)-1) -->+
  LC (lenL+1+(i*3+lenR*3+2)) ((k*2+1)*2^(i*3+lenR*3+2)-1) |> RC 1.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_1 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (((x*2+1)*2^i0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+1+(i*3+lenR*3+4)) ((k*2+1)*2^(i*3+lenR*3+4)-1) |> RC1 i0 ((2^i0-1)*2+1) x.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_0_1_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+1+(i*3+lenR*3+4)) ((k*2+1)*2^(i*3+lenR*3+4)-1) |> RC 0.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1_0 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (((x*2+1)*2^i0*2+1)*2^(i*2)-1) -->+
  LC (lenL+1+(i*3+lenR*3+4)) ((k*2+1)*2^(i*3+lenR*3+4)-1) |> RC1 i0 ((2^i0-1)*2+1) x.
Proof.
  solve_rule ROv2_1_0.
Qed.

Lemma RC2_Ov_1_0_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((0*2+1)*2^(i*2)-1) -->+
  LC (lenL+1+(i*3+lenR*3+4)) ((k*2+1)*2^(i*3+lenR*3+4)-1) |> RC 0.
Proof.
  solve_rule ROv2_1_0.
Qed.

Lemma RC2_Ov_1_1 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (((x*2+1)*2^i0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+1+(i*3+lenR*3+5)) ((k*2+1)*2^(i*3+lenR*3+5)-1) |> RC2 i0 ((2^i0-1)*2) x.
Proof.
  solve_rule ROv2_1_1.
Qed.

Lemma RC2_Ov_1_1_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+1+(i*3+lenR*3+5)) ((k*2+1)*2^(i*3+lenR*3+5)-1) |> RC 1.
Proof.
  solve_rule ROv2_1_1.
Qed.



Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1 <> 2^lenL)
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
      spl.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        rw_pa.
        spl.
        destruct n'.
        1: lia.
        replace (S n'*3) with (n'*3+3) by lia.
        solve_v1 k lenL (n'*3).
      * eex cfgR2.
        1: apply RC1_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc; finish.
        solve_v1 k lenL (n'*3).
      * eex cfgR1.
        1: apply RC1_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eex cfgR2.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    divmod2_cases lenR.
    + divmod2_cases i.
      * lowbit_cases x.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'0*3+n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_0_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases x.
        {
          eex cfgL.
          1: follow10 RC2_Ov_0_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'0*3+n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_0_1; lia.
          spl.
          zify_le_mul_r; lia.
        }
    + divmod2_cases i.
      * lowbit_cases x.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_0_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'0*3+n'*3).
        }
        {
          eex cfgR1.
          1: apply RC2_Ov_1_0; lia.
          spl.
          zify_le_mul_r; lia.
        }
      * lowbit_cases x.
        {
          eex cfgL.
          1: follow10 RC2_Ov_1_1_0; follow100 RC_Inc; finish.
          spl.
          solve_v1 k lenL (n'0*3+n'*3).
        }
        {
          eex cfgR2.
          1: apply RC2_Ov_1_1; lia.
          spl.
          zify_le_mul_r; lia.
        }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 19 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM39.


