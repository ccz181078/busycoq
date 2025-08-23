From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

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

