From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat.
Require Import Lia PeanoNat String.
From BusyCoq Require ES_v2.

Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0] len n (rd1 *> BinInc rd1 m). 

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
  unfold LC,RC,RC1;
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

Module TM32.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_0LD0RC_1LE1RB_0LF0LE_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> rd0 *> r -->+
  l <| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{F}} [0;1;1;1;1;1;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1;1;1;1] {{B}}> r) (at level 30).

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <1| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma LOv_O r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(1+n) |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n |> rd1 *> [0] *> r.
Proof.
  ES_v2.es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [0;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma ROv_O l r:
  l |> [0;1;0] *> r -->+
  l <* ld1 |> r.
Proof.
  es.
Qed.

Lemma ROv1_S l r n:
  l |1> rd1^^(1+n) *> [0;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma ROv1_O l r n:
  l <* ld0 <* ld1^^n |1> [0;1;0] *> r -->+
  l <* ld1 <* ld0^^(1+n) |> r.
Proof.
  es.
Qed.


Definition RC1 len n m := BinDec rd0 rd1 len n ([0;1;0;0] *> BinInc rd1 m). 

Ltac solve_rule H :=
  intros;
  unfold LC,RC,RC1;
  rw_Bin; try solve[solve_pow2_lt]; follow' H.

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

Lemma RC1_Inc len n m l:
  1+n<2^len ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
Proof.
  intros H.
  apply RBinDec_spec; try lia.
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

Lemma RC1_Inc1 len n m l:
  1+n<2^len ->
  l |1> RC1 len (1+n) m -->+
  l <1| RC1 len n m.
Proof.
  intros H.
  apply RBinDec_spec; try lia.
  follow' RInc1.
Qed.


Lemma LC_Ov_0 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1) (2^(lenL+1)-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule LOv_O.
Qed.

Lemma LC_Ov_1 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2) -->+
  LC lenL (2^lenL-1) |> RC1 (i+1) ((2^i-1)*2) x.
Proof.
  solve_rule LOv_S.
Qed.

Lemma LC_Ov1 lenL x i:
  LC lenL 0 <1| RC ((x*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i (2^i-1) x.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv_S.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2) |> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 0 -->+
  LC (lenL+1) (k*2) |> RC 0.
Proof.
  epose proof (ROv_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv1_S.
Qed.

Lemma RC1_Ov1_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv1_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_0 lenL k x i:
  k+1<2^lenL ->
  LC lenL (k+1) |1> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2+1) |> RC1 i (2^i-1) x.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split_lt x0 i0 lenL).
  rewrite (lowbit_split x0 i0 lenL) in * by lia.
  repeat rewrite Nat.add_sub in H0.
  solve_rule ROv1_O.
Qed.

Lemma RC1_Ov1_0_0 lenL k:
  k+1<2^lenL ->
  LC lenL (k+1) |1> RC1 0 0 0 -->+
  LC (lenL+1) (k*2+1) |> RC 0.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split_lt x i lenL).
  rewrite (lowbit_split x i lenL) in * by lia.
  repeat rewrite Nat.add_sub in H0.
  epose proof (ROv1_O _ 0inf) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgL' lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR)
| cfgR1' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    2:{
      eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
    }
    divmod2_cases n.
    + lowbit_cases n'.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov_1.
      pose proof (split_bound_v2 x i).
      spl.
    + lowbit_cases n'.
      1: lia.
      eex cfgR1'.
      1: apply LC_Ov_0.
      pose proof (split_bound_v2 x i).
      spl.
  - destruct k as [|k].
    2:{
      eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
    }
    lowbit_cases n.
    1: lia.
    eex cfgR1.
    1: apply LC_Ov1.
    pose proof (split_bound_v1 x i lenL).
    spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    destruct lenR.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR1.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc1; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1'.
        1: apply RC1_Ov_1; lia.
        spl.
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    destruct lenR.
    + remember (k-1) as k'.
      replace k with (k'+1) in * by lia.
      lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov1_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR1.
        1: apply RC1_Ov1_0; lia.
        pose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov1_1_0; follow100 RC_Inc1; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1'.
        1: apply RC1_Ov1_1; lia.
        spl.
        zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 11 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM32.


Module TM33.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_0LD1LE_1LE1RB_0LF0LE_1RA0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{F}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof.
  es.
Qed.

Lemma RInc l r n:
  l |> rd1^^n *> rd0 *> r -->+
  l <| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{F}} [0;1;1;1;1;1;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1;1;1;1] {{B}}> r) (at level 30).

Lemma RInc1 l r n:
  l |1> rd1^^n *> rd0 *> r -->+
  l <1| rd0^^n *> rd1 *> r.
Proof.
  es.
Qed.

Lemma LInc1 l r n:
  l <* ld0 <* ld1^^n <1| r -->+
  l <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma LOv_O r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(1+n) |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv_S r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n |> rd1 *> [0] *> r.
Proof.
  ES_v2.es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [0;1;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma ROv_O l r:
  l |> [0;1;0] *> r -->+
  l <* ld1 |> r.
Proof.
  es.
Qed.

Lemma ROv1_S l r n:
  l |1> rd1^^(1+n) *> [0;1;0] *> r -->+
  l <* ld1 <* ld1 <* ld0^^n |1> r.
Proof.
  es.
Qed.

Lemma ROv1_O l r n:
  l <* ld0 <* ld1^^n |1> [0;1;0] *> r -->+
  l <* ld1 <* ld0^^(1+n) |> r.
Proof.
  es.
Qed.


Definition RC1 len n m := BinDec rd0 rd1 len n ([0;1;0;0] *> BinInc rd1 m). 

Ltac solve_rule H :=
  intros;
  unfold LC,RC,RC1;
  rw_Bin; try solve[solve_pow2_lt]; follow' H.

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

Lemma RC1_Inc len n m l:
  1+n<2^len ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
Proof.
  intros H.
  apply RBinDec_spec; try lia.
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

Lemma RC1_Inc1 len n m l:
  1+n<2^len ->
  l |1> RC1 len (1+n) m -->+
  l <1| RC1 len n m.
Proof.
  intros H.
  apply RBinDec_spec; try lia.
  follow' RInc1.
Qed.


Lemma LC_Ov_0 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1) (2^(lenL+1)-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule LOv_O.
Qed.

Lemma LC_Ov_1 lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i*2) -->+
  LC lenL (2^lenL-1) |> RC1 (i+1) ((2^i-1)*2) x.
Proof.
  solve_rule LOv_S.
Qed.

Lemma LC_Ov1 lenL x i:
  LC lenL 0 <1| RC ((x*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i (2^i-1) x.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv_S.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2) |> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 0 -->+
  LC (lenL+1) (k*2) |> RC 0.
Proof.
  epose proof (ROv_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |1> RC1 i (2^i-1) x.
Proof.
  solve_rule ROv1_S.
Qed.

Lemma RC1_Ov1_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |1> RC 0.
Proof.
  epose proof (ROv1_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_0 lenL k x i:
  k+1<2^lenL ->
  LC lenL (k+1) |1> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2+1) |> RC1 i (2^i-1) x.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split_lt x0 i0 lenL).
  rewrite (lowbit_split x0 i0 lenL) in * by lia.
  repeat rewrite Nat.add_sub in H0.
  solve_rule ROv1_O.
Qed.

Lemma RC1_Ov1_0_0 lenL k:
  k+1<2^lenL ->
  LC lenL (k+1) |1> RC1 0 0 0 -->+
  LC (lenL+1) (k*2+1) |> RC 0.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split_lt x i lenL).
  rewrite (lowbit_split x i lenL) in * by lia.
  repeat rewrite Nat.add_sub in H0.
  epose proof (ROv1_O _ 0inf) as I1.
  solve_rule I1.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgL' lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR)
| cfgR1' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    2:{
      eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
    }
    divmod2_cases n.
    + lowbit_cases n'.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov_1.
      pose proof (split_bound_v2 x i).
      spl.
    + lowbit_cases n'.
      1: lia.
      eex cfgR1'.
      1: apply LC_Ov_0.
      pose proof (split_bound_v2 x i).
      spl.
  - destruct k as [|k].
    2:{
      eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      spl.
    }
    lowbit_cases n.
    1: lia.
    eex cfgR1.
    1: apply LC_Ov1.
    pose proof (split_bound_v1 x i lenL).
    spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    destruct lenR.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR1.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc1; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1'.
        1: apply RC1_Ov_1; lia.
        spl.
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    destruct lenR.
    + remember (k-1) as k'.
      replace k with (k'+1) in * by lia.
      lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov1_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR1.
        1: apply RC1_Ov1_0; lia.
        pose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov1_1_0; follow100 RC_Inc1; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1'.
        1: apply RC1_Ov1_1; lia.
        spl.
        zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 11 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM33.


Module TM111.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC0RE_1RF0LE_0RA---").
(* similar to TM108 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

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
  solve_LOverflow.
Qed.


Lemma ROv_SS l r n m:
  l |> rd1^^n *> [1] *> rd1^^(3+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd1 *> rd0^^m *> rd1 *> r.
Proof.
  ES_v2.es.
Qed.

Lemma ROv_SO l r n m:
  l |> rd1^^n *> [1] *> rd1^^2 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd0^^(1+m) *> rd1 *> r.
Proof.
  ES_v2.es.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <| [1] *> r.
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

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
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
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) <| RC1 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (0*2) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) <| RC 1.
Proof.
  epose proof (ROv_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (((x*2+1)*2^i-1)*2*2+1) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) |> RC1 (i+1) ((2^(i+1)-1)*2) x.
Proof.
  solve_rule ROv_SO.
Qed.

Lemma RC1_Ov_2 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2+1) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) |> RC1 0 0 (m+1).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv_SS.
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

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
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
    2:{
      eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
    }
    lowbit_cases n.
    1: lia.
    eex cfgR1.
    1: apply LC_Ov.
    pose proof (split_bound_v1 x i lenL).
    spl.
  - destruct n as [|n].
    2:{
      destruct k.
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases m.
    {
      lowbit_cases n'.
      - eex cfgL.
        1: apply RC1_Ov_0_0; lia.
        spl.
        solve_v1 k lenL lenR.
      - eex cfgR1.
        1: follow10 RC1_Ov_0.
        1: rewrite (Nat.add_comm (_*2) 1).
        1: follow100 LC_Inc.
        1: rewrite Nat.add_comm; solve_pow2_lt.
        1: finish.
        spl.
        zify_le_mul_r; lia.
    }
    divmod2_cases n'.
    {
      lowbitS_cases n'0.
      eex cfgR1.
      1: apply RC1_Ov_1; lia.
      spl; rw_pa; zify_le_mul_r; lia.
    }
    {
      eex cfgR1.
      1: apply RC1_Ov_2; lia.
      spl.
      zify_le_mul_r; lia.
    }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 6 27 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM111.


Module TM108.
Definition tm := Eval compute in (TM_from_str "1RB0LA_0RC---_1LD1RF_1LE0LD_1RC1LE_1RE0RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{C}}> r) (at level 30).

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
  solve_LOverflow.
Qed.


Lemma ROv_SS l r n m:
  l |> rd1^^n *> [1] *> rd1^^(3+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd1 *> rd0^^m *> rd1 *> r.
Proof.
  ES_v2.es.
Qed.

Lemma ROv_SO l r n m:
  l |> rd1^^n *> [1] *> rd1^^2 *> rd0 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [1] *> rd0^^(1+m) *> rd1 *> r.
Proof.
  ES_v2.es.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) <| [1] *> r.
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

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
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
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) <| RC1 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (0*2) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) <| RC 1.
Proof.
  epose proof (ROv_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (((x*2+1)*2^i-1)*2*2+1) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) |> RC1 (i+1) ((2^(i+1)-1)*2) x.
Proof.
  solve_rule ROv_SO.
Qed.

Lemma RC1_Ov_2 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2+1) -->+
  LC (lenL+1+lenR+1) (((k*2+1)*2^lenR-1)*2+1) |> RC1 0 0 (m+1).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv_SS.
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

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
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
    2:{
      eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
    }
    lowbit_cases n.
    1: lia.
    eex cfgR1.
    1: apply LC_Ov.
    pose proof (split_bound_v1 x i lenL).
    spl.
  - destruct n as [|n].
    2:{
      destruct k.
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases m.
    {
      lowbit_cases n'.
      - eex cfgL.
        1: apply RC1_Ov_0_0; lia.
        spl.
        solve_v1 k lenL lenR.
      - eex cfgR1.
        1: follow10 RC1_Ov_0.
        1: rewrite (Nat.add_comm (_*2) 1).
        1: follow100 LC_Inc.
        1: rewrite Nat.add_comm; solve_pow2_lt.
        1: finish.
        spl.
        zify_le_mul_r; lia.
    }
    divmod2_cases n'.
    {
      lowbitS_cases n'0.
      eex cfgR1.
      1: apply RC1_Ov_1; lia.
      spl; rw_pa; zify_le_mul_r; lia.
    }
    {
      eex cfgR1.
      1: apply RC1_Ov_2; lia.
      spl.
      zify_le_mul_r; lia.
    }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 11 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM108.


Module TM107.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1RD_0LE1RE_1RF0RC_1RA---").
(* similar to TM100 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{E}} [0;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1] {{A}}> r) (at level 30).

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

Lemma LOv_S r n m:
  ldh <* ld1^^(n+1) <| rd1^^(m+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^2 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma LOv_O r n:
  ldh <* ld1^^(n+1) <| rd0 *> r -->+
  ldh <* ld0^^n <| rd0^^2 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^(n+1) *> [1;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^m <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_S l r n m k:
  l <* ld0 <* ld1^^n |> [1;1;0;0] *> rd1^^m *> rd0 *> rd1^^(1+k) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1^^3 <* ld0^^k <| rd1 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
Qed.

Lemma ROv_O_O l r n m:
  l <* ld0 <* ld1^^n |> [1;1;0;0] *> rd1^^m *> rd0 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(m+n) <* ld1 <| rd0^^2 *> [1] *> r.
Proof.
  execute_with_shift_rule'.
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

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov_1 lenL x i0 i:
  LC (lenL+1) 0 <| RC (((x*2+1)*2^i0*2+1)*2^(i+1)-1) -->+
  LC (lenL+1+1+i) (((2^lenL-1)*2*2+1)*2^i-1) <| RC1 (i0+1) ((2^i0-1)*2*2) x.
Proof.
  solve_rule LOv_S.
Qed.

Lemma LC_Ov_1_0 lenL i:
  LC (lenL+1) 0 <| RC ((0*2+1)*2^(i+1)-1) -->+
  LC (lenL+1+1+i) (((2^lenL-1)*2*2+1)*2^i-1) <| RC 3.
Proof.
  solve_rule LOv_S.
Qed.

Lemma LC_Ov_0 lenL x i0:
  LC (lenL+1) 0 <| RC ((x*2+1)*2^i0*2) -->+
  LC (lenL) (2^lenL-1) <| RC1 (i0+1+1) (((2^i0-1)*2*2+1)*2+1) x.
Proof.
  solve_rule LOv_O.
Qed.

Lemma LC_Ov_0_0 lenL:
  LC (lenL+1) 0 <| RC (0*2) -->+
  LC (lenL) (2^lenL-1) <| RC 4.
Proof.
  epose proof (LOv_O 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i0 i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR+1) 0 (((x*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) ((((k*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC1 (i0+1) ((2^i0-1)*2*2) x.
Proof.
  solve_rule ROv_S.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR i:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR+1) 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) ((((k*2+1)*2^lenR-1)*2+1)*2^i-1) <| RC 3.
Proof.
  solve_rule ROv_S.
Qed.


Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL /\ lenL>=2 /\
  k+n <> 2^(lenL-2) /\
  k+n <> 2^(lenL-2)*2 /\
  k+n <> 2^(lenL-2)*3
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\ lenL>=2 /\ lenR>=1
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\ lenL>=2 /\ lenR>=1
end.

Lemma split_bound x i len:
  (x*2+1)*2^i < 2^len*4 ->
  (x*2+1)*2^i <> 2^len ->
  (x*2+1)*2^i <> 2^len*2 ->
  (x*2+1)*2^i <> 2^len*3 ->
  (2^i-1)*4+x < 2^len*2.
Proof.
  intros.
  pp_pow2_lt_le i (len+2).
  assert (i<=len+1) by lia.
  destruct (Nat.eqb_spec i (len+1)).
  {
    subst i.
    rw_pa.
    destruct x; lia.
  }
  destruct (Nat.eqb_spec i (len)).
  {
    subst i.
    rw_pa.
    destruct x as [|[|x]]; lia.
  }
  destruct (Nat.eqb_spec (i+1) (len)).
  {
    subst len.
    rw_pa.
    destruct x as [|[|[|[|x]]]]; lia.
  }
  assert (2^i*4<=2^len) by (pp_pow2_lt_le (i+1) len; lia).
  destruct (Nat.leb_spec x (2^len)).
  1: lia.
  destruct i.
  1: lia.
  cbn[Nat.pow] in *.
  rewrite Nat.mul_assoc in *.
  zify_le_mul_r; lia.
Qed.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    2:{
      eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      spl.
    }
    remember (lenL-2) as lenL'.
    replace lenL with (lenL'+1+1) in * by lia.
    clear HeqlenL'.
    lowbitS_cases n.
    destruct i.
    + lowbit_cases x.
      * eex cfgL.
        1: apply LC_Ov_0_0.
        spl.
      * rewrite Nat.mul_1_r,Nat.add_sub.
        eex cfgL1.
        1: apply LC_Ov_0.
        spl.
        2: destruct lenL'; lia.
        rw_pa.
        pose proof (split_bound x0 (i+1) lenL').
        rw_pa; lia.
    + replace (S i) with (i+1) in * by lia.
      lowbit_cases x.
      * eex cfgL.
        1: apply LC_Ov_1_0.
        spl.
        all: replace (lenL'+1+1+1+i-2) with (lenL'+1+i) by lia.
        all: rw_pa.
        -- lia.
        -- zify_le_mul_r; lia.
        -- zify_pow2sub1; lia.
      * eex cfgL1.
        1: apply LC_Ov_1.
        spl.
        2: rw_pa; zify_pow2sub1; lia.
        pose proof (split_bound_v1 x0 (i0+1) (lenL'+2)).
        rw_pa; zify_le_mul_r; lia.
  - destruct k.
    1: lia.
    eex cfgR1.
    1: apply LC_Inc; lia.
    spl.
  - destruct n as [|n].
    2:{
      destruct k.
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    remember (lenR-1) as lenR'.
    replace lenR with (lenR'+1) in * by lia.
    clear HeqlenR'.
    lowbitS_cases m.
    lowbit_cases x.
    + eex cfgL.
      1: apply RC1_Ov_1_0; lia.
      spl.
      1: solve_v1 k lenL (lenR'+i).
      all: remember (lenL-2) as lenL'.
      all: replace lenL with (lenL'+1+1) in * by lia; clear HeqlenL'.
      all: replace (lenL'+1+1+1+lenR'+1+i-2) with (lenL'+1+lenR'+1+i) by lia.
      all: rw_pa.
      all: destruct i as [|[|i]]; [lia| |cbn[Nat.pow]; lia].
      * epose proof (Nat.mul_cancel_r (k*2+1) (2^lenL'*2) (2^lenR'*4)). lia.
      * epose proof (Nat.mul_cancel_r (k*2+1) (2^lenL'*4) (2^lenR'*4)). lia.
      * epose proof (Nat.mul_cancel_r (k*2+1) (2^lenL'*6) (2^lenR'*4)). lia.
    + eex cfgL1.
      1: apply RC1_Ov_1; lia.
      spl.
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 89 3)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM107.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC0LB_1RE0RD_1RA1RE_1LB1RF_1RC0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;0;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1] {{E}}> r) (at level 30).

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
  solve_LOverflow.
Qed.

Lemma ROv_1 l r n:
  l |> rd1^^n *> [1] *> rd1^^2 *> r -->+
  l <* ld1 <* ld0^^n |> [0] *> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv_0 l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) |> [0] *> r.
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

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
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

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i*2+1) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC1 (i+1) (((2^i-1)*2+1)*2+1) x.
Proof.
  solve_rule ROv_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (0*2+1) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC 0.
Proof.
  solve_rule ROv_1.
Qed.

Lemma RC1_Ov_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+lenR+1) ((k*2+1)*2^lenR*2) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (0*2) -->+
  LC (lenL+1+lenR+1) ((k*2+1)*2^lenR*2) |> RC 0.
Proof.
  epose proof (ROv_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR1_1(lenL k lenR n x i:nat)
| cfgR1_1_0(lenL k lenR n:nat)
| cfgR1_0(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR1_1 lenL k lenR n x i => LC lenL k |> RC1 lenR n ((x*2+1)*2^i*2+1)
| cfgR1_1_0 lenL k lenR n => LC lenL k |> RC1 lenR n 1
| cfgR1_0 lenL k lenR n m => LC lenL k |> RC1 lenR n (m*2)
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
| cfgR1_1 lenL k lenR n x i => n+(x*2+1)*2^i+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
  (x=O -> n+2^i*4<=k)
| cfgR1_1_0 lenL k lenR n => n+0+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1_0 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
      epose proof (split_bound_v1 x i lenL).
      divmod2_cases x.
      * eex cfgR1_0.
        1: apply LC_Ov.
        spl.
      * lowbit_cases n'.
        {
          eex cfgR1_1_0.
          1: apply LC_Ov.
          spl.
        }
        {
          eex cfgR1_1.
          1: apply LC_Ov.
          spl.
          intros; subst.
          cbn in *.
          zify_pow2sub1; lia.
        }
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1_1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases x.
    + eex cfgR1_0.
      1: apply RC1_Ov_1; lia.
      spl.
      destruct n'; zify_le_mul_r; lia.
    + lowbit_cases n'.
      * eex cfgR1_1_0.
        1: apply RC1_Ov_1; lia.
        spl.
        zify_le_mul_r; lia.
      * eex cfgR1_1.
        1: apply RC1_Ov_1; lia.
        spl.
        1: zify_le_mul_r; lia.
        intros; subst.
        cbn in *.
        zify_pow2sub1; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1_1_0.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    eex cfgL.
    1: follow10 RC1_Ov_1_0; follow100 RC_Inc; finish.
    spl.
    solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1_0.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
      spl.
    + divmod2_cases x.
      * eex cfgR1_0.
        1: apply RC1_Ov_0; lia.
        spl.
        destruct n'; zify_le_mul_r; lia.
      * lowbit_cases n'.
        { eex cfgR1_1_0.
          1: apply RC1_Ov_0; lia.
          spl.
          zify_le_mul_r; lia. }
        { eex cfgR1_1.
          1: apply RC1_Ov_0; lia.
          spl.
          1: zify_le_mul_r; lia.
          intros; subst.
          cbn in *.
          zify_pow2sub1; lia. }
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 7 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM3.


Module TM96.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RC1RE_0RF0RA_0RC---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1;1] {{A}}> r) (at level 30).

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
  solve_LOverflow.
Qed.

Lemma ROv_S l r n m:
  l |> rd1^^n *> [1] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n |> rd0^^(1+m) *> [0] *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv_O l r n:
  l |> rd1^^n *> [1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(1+n) |> [0] *> r.
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

Lemma RC1_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC1 len (1+n) m -->+
  l <| RC1 len n m.
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

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^(1+i)-1) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC1 (1+i) ((2^(1+i)-1)*2+1) x.
Proof.
  solve_rule ROv_S.
Qed.

Lemma RC1_Ov_0 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i*2) -->+
  LC (lenL+1+(1+lenR)) ((k*2+1)*2^(1+lenR)-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (0*2) -->+
  LC (lenL+1+(1+lenR)) ((k*2+1)*2^(1+lenR)-1) |> RC 0.
Proof.
  epose proof (ROv_O _ 0inf _) as I1.
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

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => k<2^lenL /\ 1 <= k+n < 2^lenL
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
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    destruct i as [|i].
    + replace ((x*2+1)*2^0-1) with (x*2) in * by lia.
      lowbit_cases x.
      * eex cfgL.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: apply RC1_Ov_0; lia.
        spl.
        solve_v1 k lenL lenR.
    + eex cfgR1.
      1: apply RC1_Ov_1; lia.
      spl.
      replace (S i) with (1+i) in * by lia.
      rw_pa.
      epose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 29 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM96.


Module TM110.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1RA1RD_1RE1RF_1RB0LE_1LE0RC").
(* simular to TM81 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{F}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;0;1;1;1;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^(n) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(1+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r:
  l |2> rd0 *> r -->+
  l <* ld1 |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+m+n) |2> r.
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

Lemma LC_Ov lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+i) (((2^lenL-1)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC ((x*2+1)*2^i*2) -->+
  LC (lenL+1) (k*2) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |2> RC (0*2) -->+
  LC (lenL+1) (k*2) |> RC 0.
Proof.
  epose proof (ROv2_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+i+lenR)) ((k*2+1)*2^(1+i+lenR)) |2> RC x.
Proof.
  solve_rule ROv.
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
    + lowbitS_cases n.
      eex cfgR'.
      1: apply LC_Ov.
      spl.
      zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - divmod2_cases n.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC_Ov2_0_0; follow100 RC_Inc; finish.
        spl.
      * eex cfgR1.
        1: apply RC_Ov2_0; lia.
        epose proof (split_bound_v2 x i).
        spl.
    + lowbitS_cases n'.
      eex cfgR'.
      1: apply RC_Ov2_1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
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

End TM110.


Module TM81.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0LB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0^^(1+m) |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld1 <* ld0^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <* ld1 <* ld0^^n |> rd0 *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^n <* ld1 <* ld0^^m |2> r.
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

Lemma LC_Ov lenL x i:
  LC (1+lenL) 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+i+1) ((((2^lenL-1)*2+1)*2^i-1)*2+1) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i-1) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL k x i:
  k+1<2^lenL ->
  LC lenL (k+1) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k |> RC1 (i+1) ((2^i-1)*2*2+1) x.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split x0 i0 lenL).
  epose proof (lowbit_split_lt x0 i0 lenL).
  rewrite H0 by lia.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL k:
  k+1<2^lenL ->
  LC lenL (k+1) |2> RC (0*2) -->+
  LC lenL k |> RC 2.
Proof.
  intros.
  lowbitS_cases k.
  rewrite Nat.sub_add in * by lia.
  epose proof (lowbit_split x i lenL).
  epose proof (lowbit_split_lt x i lenL).
  rewrite H0 by lia.
  epose proof (ROv2_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+lenR+1+i) ((((k*2+1)*2^lenR-1)*2+1)*2^i-1) |2> RC x.
Proof.
  solve_rule ROv.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR'(lenL k x i:nat)
| cfgR'_0(lenL k:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR' lenL k x i => LC lenL k |2> RC ((x*2+1)*2^i)
| cfgR'_0 lenL k => LC lenL k |2> RC 0
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ k+n < 2^lenL
| cfgR' lenL k x i => (x*2+1)*2^i < k < 2^lenL /\
  (x=O -> 2^i*2<=k+1)
| cfgR'_0 lenL k => lenL<>O /\ 0 < k /\ k+2 < 2^lenL
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
    + lowbitS_cases n.
      destruct lenL. 1: lia.
      cbn[Nat.pow] in *.
      lowbit_cases x.
      * eex cfgR'_0.
        1: apply LC_Ov.
        spl.
      * eex cfgR'.
        1: apply LC_Ov.
        spl.
        -- zify_pow2sub1; lia.
        -- zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - destruct i.
    + rewrite Nat.mul_1_r.
      lowbitS_cases x.
      lowbit_cases x0.
      * eex cfgR'_0.
        1: apply RC_Ov2_1; lia.
        spl.
        solve_v1 k lenL i.
      * eex cfgR'.
        1: apply RC_Ov2_1; lia.
        spl.
        -- zify_pow2sub1; lia.
        -- zify_le_mul_r; lia.
    + replace (S i) with (i+1) in * by lia.
      rw_pa.
      rewrite Nat.mul_assoc in *.
      replace k with (k-1+1) in * by lia.
      eex cfgR1.
      1: apply RC_Ov2_0; lia.
      spl.
      destruct x.
      1: lia.
      zify_le_mul_r; lia.
  - replace k with (k-1+1) in * by lia.
    eex cfgL.
    1: follow10 RC_Ov2_0_0; follow100 RC_Inc; finish.
    spl.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    lowbit_cases x.
    + eex cfgR'_0.
      1: apply RC1_Ov; lia.
      spl.
      1: zify_le_mul_r; lia.
      solve_v1 k lenL (lenR+i).
    + eex cfgR'.
      1: apply RC1_Ov; lia.
      spl.
      1: zify_le_mul_r; lia.
      intros; subst.
      rw_pa.
      zify_pow2sub1; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 0)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM81.


Module TM67.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RE_1LF1RB_0LB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;0;1;1] {{E}}> r) (at level 30).

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
  solve_LOverflow.
Qed.

Lemma ROv_S l r n:
  l |> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld0 <* ld1 <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Notation "l <1| r" := (l <{{B}} [0;1;1;1;1;1;0] *> r) (at level 30).
Notation "l |1> r" := (l <* [1;0;1;1;1;1;1] {{E}}> r) (at level 30).

Lemma ROv_O l r:
  l |> [1] *> rd1 *> r -->+
  l <* ld1 |1> [1] *> r.
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

Lemma ROv1_S l r n:
  l |1> rd1^^(1+n) *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld1 <* ld0^^n |> [0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_O l r:
  l |1> [1] *> rd1 *> r -->+
  l <* ld1 |1> [0] *> r.
Proof.
  es.
Qed.

Lemma LOv1 r n:
  ldh <* ld1^^n <1| r -->+
  ldh <* ld0^^n |> [0] *> r.
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
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov1 lenL n i:
  LC lenL O <1| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv1.
Qed.

Lemma RC1_Ov_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv_S.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2+1)*2+1)*2^lenR-1) |> RC 0.
Proof.
  epose proof (ROv_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2) |1> RC1 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv_O.
Qed.

Lemma RC1_Ov_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |> RC1 0 0 0 -->+
  LC (lenL+1) (k*2) |1> RC 1.
Proof.
  epose proof (ROv_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_1 lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1_S.
Qed.

Lemma RC1_Ov1_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |1> RC1 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR) (((k*2)*2+1)*2^lenR-1) |> RC 0.
Proof.
  epose proof (ROv1_S _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov1_0 lenL k x i:
  k<2^lenL ->
  LC lenL k |1> RC1 0 0 ((x*2+1)*2^i) -->+
  LC (lenL+1) (k*2) |1> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv1_O.
Qed.

Lemma RC1_Ov1_0_0 lenL k:
  k<2^lenL ->
  LC lenL k |1> RC1 0 0 0 -->+
  LC (lenL+1) (k*2) |1> RC 0.
Proof.
  epose proof (ROv1_O _ 0inf) as I1.
  solve_rule I1.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgL'(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR1'(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgL' lenL k n => LC lenL k <1| RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR1' lenL k lenR n m => LC lenL k |1> RC1 lenR n m
end.

Close Scope sym.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgL' lenL k n => 1 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> m=O -> k+1<>n+2^lenL)
| cfgR1' lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
      lia.
  - destruct k as [|k].
    + lowbit_cases n.
      1: lia.
      eex cfgR1.
      1: apply LC_Ov1.
      pose proof (split_bound_v1 x i lenL).
      spl.
    + eex cfgL'.
      1: follow10 LC_Inc1; follow100 RC_Inc1; finish.
      lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    destruct lenR.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov_0_0; follow100 RC_Inc1; finish.
        spl.
      * eex cfgR1'.
        1: apply RC1_Ov_0; lia.
        epose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov_1_0; follow100 RC_Inc; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: apply RC1_Ov_1; lia.
        spl.
        1: zify_le_mul_r; lia.
        intros; subst.
        solve_v1 k lenL lenR.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1'.
      1: follow10 RC1_Inc1; follow100 LC_Inc1; finish.
      spl.
    }
    destruct lenR.
    + lowbit_cases m.
      * eex cfgL'.
        1: follow10 RC1_Ov1_0_0; follow100 RC_Inc1; finish.
        spl.
      * eex cfgR1'.
        1: apply RC1_Ov1_0; lia.
        epose proof (split_bound_v2 x i).
        spl.
    + lowbit_cases m.
      * eex cfgL.
        1: follow10 RC1_Ov1_1_0; follow100 RC_Inc; finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: apply RC1_Ov1_1; lia.
        spl.
        1: zify_le_mul_r; lia.
        intros; subst.
        solve_v1 k lenL lenR.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL' 3 3 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM67.


Module TM27.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RE_1LD0RB_1RA0LD_1RF1RC_0RA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{C}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{B}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
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

Lemma LC_Ov lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+1+i) ((((2^lenL-1)*2+1)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL i2 k x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k <| RC1 (i+1+i2) ((((2^i-1)*2+1)*2^i2-1)*2+1) x.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL i2 k:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC (0*2) -->+
  LC lenL k <| RC (2^i2*2).
Proof.
  epose proof (ROv2_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR)+1+i) (((k*2+1)*2^(1+lenR)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv.
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
| cfgL lenL k n => k<2^lenL /\ k+n+1 < 2^lenL*2 /\ k+n+1 <> 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\ m mod 2 = 1
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
    + lowbitS_cases n.
      divmod2_cases x.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0_0.
          1: rw_pa; lia.
          1: finish.
          spl.
          pp_pow2_lt_le i (lenL+1).
          lia.
        }
        {
          eex cfgR1.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0.
          1: rw_pa; lia.
          1: rewrite (Nat.add_comm ((2^lenL-1)*2)).
          1: follow100 LC_Inc.
          1: rw_pa; lia.
          1: finish.
          spl.
          zify_pow2sub1; lia.
        }
      * eex cfgR'.
        1: apply LC_Ov.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - divmod2_cases n.
    1: lia.
    lowbitS_cases n'.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
      * remember (k-1) as k'.
        replace k with (k'+1) in * by lia.
        clear k Heqk'.
        eex cfgR1.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k'+1)*2) with (1+(k'*2+1)) by lia.
        1: follow100 LC_Inc.
        1: spl.
        1: finish.
        spl.
        zify_pow2sub1; lia.
    + eex cfgR'.
      1: apply RC_Ov2_1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k*2+1)*2^(1+lenR)) with (1+((k*2+1)*2^(1+lenR)-1)) by lia.
        1: follow100 LC_Inc.
        1: solve_v1 k lenL lenR.
        1: finish.
        spl.
        rw_pa.
        zify_pow2sub1; lia.
    + lowbitS_cases n'.
      eex cfgR'.
      1: follow10 RC1_Ov; finish.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 83 3)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM27.


Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC1LB_0RD1RE_1LA0RC_1RF1RD_0RB---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{D}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{C}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
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

Lemma LC_Ov lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+1+i) ((((2^lenL-1)*2+1)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL i2 k x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k <| RC1 (i+1+i2) ((((2^i-1)*2+1)*2^i2-1)*2+1) x.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL i2 k:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC (0*2) -->+
  LC lenL k <| RC (2^i2*2).
Proof.
  epose proof (ROv2_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR)+1+i) (((k*2+1)*2^(1+lenR)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv.
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
| cfgL lenL k n => k<2^lenL /\ k+n+1 < 2^lenL*2 /\ k+n+1 <> 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\ m mod 2 = 1
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
    + lowbitS_cases n.
      divmod2_cases x.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0_0.
          1: rw_pa; lia.
          1: finish.
          spl.
          pp_pow2_lt_le i (lenL+1).
          lia.
        }
        {
          eex cfgR1.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0.
          1: rw_pa; lia.
          1: rewrite (Nat.add_comm ((2^lenL-1)*2)).
          1: follow100 LC_Inc.
          1: rw_pa; lia.
          1: finish.
          spl.
          zify_pow2sub1; lia.
        }
      * eex cfgR'.
        1: apply LC_Ov.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - divmod2_cases n.
    1: lia.
    lowbitS_cases n'.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
      * remember (k-1) as k'.
        replace k with (k'+1) in * by lia.
        clear k Heqk'.
        eex cfgR1.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k'+1)*2) with (1+(k'*2+1)) by lia.
        1: follow100 LC_Inc.
        1: spl.
        1: finish.
        spl.
        zify_pow2sub1; lia.
    + eex cfgR'.
      1: apply RC_Ov2_1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k*2+1)*2^(1+lenR)) with (1+((k*2+1)*2^(1+lenR)-1)) by lia.
        1: follow100 LC_Inc.
        1: solve_v1 k lenL lenR.
        1: finish.
        spl.
        rw_pa.
        zify_pow2sub1; lia.
    + lowbitS_cases n'.
      eex cfgR'.
      1: follow10 RC1_Ov; finish.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 3 5 3)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM34.


Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB1RE_0RC---_1RD1LC_0RE1RA_1LF0RD_1RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{E}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
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

Lemma LC_Ov lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+1+i) ((((2^lenL-1)*2+1)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL i2 k x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k <| RC1 (i+1+i2) ((((2^i-1)*2+1)*2^i2-1)*2+1) x.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL i2 k:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC (0*2) -->+
  LC lenL k <| RC (2^i2*2).
Proof.
  epose proof (ROv2_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR)+1+i) (((k*2+1)*2^(1+lenR)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv.
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
| cfgL lenL k n => k<2^lenL /\ k+n+1 < 2^lenL*2 /\ k+n+1 <> 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\ m mod 2 = 1
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
    + lowbitS_cases n.
      divmod2_cases x.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0_0.
          1: rw_pa; lia.
          1: finish.
          spl.
          pp_pow2_lt_le i (lenL+1).
          lia.
        }
        {
          eex cfgR1.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0.
          1: rw_pa; lia.
          1: rewrite (Nat.add_comm ((2^lenL-1)*2)).
          1: follow100 LC_Inc.
          1: rw_pa; lia.
          1: finish.
          spl.
          zify_pow2sub1; lia.
        }
      * eex cfgR'.
        1: apply LC_Ov.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - divmod2_cases n.
    1: lia.
    lowbitS_cases n'.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
      * remember (k-1) as k'.
        replace k with (k'+1) in * by lia.
        clear k Heqk'.
        eex cfgR1.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k'+1)*2) with (1+(k'*2+1)) by lia.
        1: follow100 LC_Inc.
        1: spl.
        1: finish.
        spl.
        zify_pow2sub1; lia.
    + eex cfgR'.
      1: apply RC_Ov2_1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k*2+1)*2^(1+lenR)) with (1+((k*2+1)*2^(1+lenR)-1)) by lia.
        1: follow100 LC_Inc.
        1: solve_v1 k lenL lenR.
        1: finish.
        spl.
        rw_pa.
        zify_pow2sub1; lia.
    + lowbitS_cases n'.
      eex cfgR'.
      1: follow10 RC1_Ov; finish.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 11 2015 3)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM36.


Module TM51.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LB_1RD1LC_0RA1RE_1RF1RA_0RC---").
(* similar to TM34 *)
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [1;1;1;1;1;1;0;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;1;0;1;1] {{A}}> r) (at level 30).

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

Notation "l |2> r" := (l <* [0;1;1;1;1;1] {{D}}> r) (at level 30).

Lemma LOv r n m:
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^(2+n) <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_S l r m:
  l |2> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1^^m |2> r.
Proof.
  es.
Qed.

Lemma ROv2_O l r n:
  l <* ld0 <* ld1^^n |2> rd0 *> r -->+
  l <| rd0^^(1+n) *> [1] *> r.
Proof.
  es.
Qed.

Lemma ROv l r n m:
  l |> rd1^^n *> [1] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld0 <* ld1^^(1+n) <* ld0 <* ld1^^m |2> r.
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

Lemma LC_Ov lenL x i:
  LC lenL 0 <| RC ((x*2+1)*2^i-1) -->+
  LC (lenL+1+1+i) ((((2^lenL-1)*2+1)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule LOv.
Qed.

Lemma RC_Ov2_1 lenL k x i:
  k<2^lenL ->
  LC lenL k |2> RC (((x*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+1+i) ((k*2*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC_Ov2_0 lenL i2 k x i:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC ((x*2+1)*2^i*2) -->+
  LC lenL k <| RC1 (i+1+i2) ((((2^i-1)*2+1)*2^i2-1)*2+1) x.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC_Ov2_0_0 lenL i2 k:
  k<2^lenL ->
  LC (lenL+1+i2) ((k*2+1)*2^i2) |2> RC (0*2) -->+
  LC lenL k <| RC (2^i2*2).
Proof.
  epose proof (ROv2_O _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i-1) -->+
  LC (lenL+1+(1+lenR)+1+i) (((k*2+1)*2^(1+lenR)*2+1)*2^i) |2> RC x.
Proof.
  solve_rule ROv.
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
| cfgL lenL k n => k<2^lenL /\ k+n+1 < 2^lenL*2 /\ k+n+1 <> 2^lenL
| cfgR' lenL k m => m < k < 2^lenL /\ m mod 2 = 1
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
    + lowbitS_cases n.
      divmod2_cases x.
      * lowbit_cases n'.
        {
          eex cfgL.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0_0.
          1: rw_pa; lia.
          1: finish.
          spl.
          pp_pow2_lt_le i (lenL+1).
          lia.
        }
        {
          eex cfgR1.
          1: follow10 LC_Ov.
          1: follow100 RC_Ov2_0.
          1: rw_pa; lia.
          1: rewrite (Nat.add_comm ((2^lenL-1)*2)).
          1: follow100 LC_Inc.
          1: rw_pa; lia.
          1: finish.
          spl.
          zify_pow2sub1; lia.
        }
      * eex cfgR'.
        1: apply LC_Ov.
        spl.
        zify_le_mul_r; lia.
    + eex cfgL.
      1: follow10 LC_Inc; follow100 RC_Inc; finish.
      lia.
  - divmod2_cases n.
    1: lia.
    lowbitS_cases n'.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
      * remember (k-1) as k'.
        replace k with (k'+1) in * by lia.
        clear k Heqk'.
        eex cfgR1.
        1: follow10 RC_Ov2_1.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k'+1)*2) with (1+(k'*2+1)) by lia.
        1: follow100 LC_Inc.
        1: spl.
        1: finish.
        spl.
        zify_pow2sub1; lia.
    + eex cfgR'.
      1: apply RC_Ov2_1; lia.
      spl.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2:{
      destruct k as [|k].
      1: lia.
      eex cfgR1.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    lowbitS_cases m.
    divmod2_cases x.
    + lowbit_cases n'.
      * eex cfgL.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0_0.
        1: spl.
        1: finish.
        spl.
        solve_v1 k lenL lenR.
      * eex cfgR1.
        1: follow10 RC1_Ov.
        1: follow100 RC_Ov2_0.
        1: spl.
        1: replace ((k*2+1)*2^(1+lenR)) with (1+((k*2+1)*2^(1+lenR)-1)) by lia.
        1: follow100 LC_Inc.
        1: solve_v1 k lenL lenR.
        1: finish.
        spl.
        rw_pa.
        zify_pow2sub1; lia.
    + lowbitS_cases n'.
      eex cfgR'.
      1: follow10 RC1_Ov; finish.
      spl.
      zify_le_mul_r; lia.
Qed.


Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 2 3 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM51.


