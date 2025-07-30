From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 Eqb.
Require Import ZifyNat.
Require Import NArith Lia PeanoNat String.

Lemma lpow_unrotate_10 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8]^^n *> a >> r.
Proof.
  simpl_rotate.
  reflexivity.
Qed.

Ltac rw_unrotate_0 ::=
  (rewrite lpow_unrotate_1 ||
  rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 ||
  rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_10).

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0;0;0].
Notation rd1 := [1;0;0;0;0].

Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0;0] len n (rd1 *> BinInc rd1 m). 
Definition RC2 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0] *> rd1 *> BinInc rd1 m). 
Definition RC3 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0] *> rd1 *> BinInc rd1 m). 
Definition RC4 len n m := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0] *> rd1 *> BinInc rd1 m). 

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
  unfold LC,RC,RC1,RC2,RC3,RC4;
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

Inductive DivMod2: nat->Prop :=
| mod2eq0(n n':nat)(Hn':n=n'*2):DivMod2 n
| mod2eq1(n n':nat)(Hn':n=n'*2+1):DivMod2 n
.

Lemma divmod2 n: DivMod2 n.
Proof.
  pose proof (Nat.Div0.div_mod n 2).
  pose proof (Nat.mod_upper_bound n 2).
  destruct (n mod 2) as [|[|]]. 3: lia.
  - eapply (mod2eq0 n (n/2)).
    lia.
  - eapply (mod2eq1 n (n/2)).
    lia.
Qed.

Ltac divmod2_cases n :=
  epose proof (divmod2 n) as Hdm2;
  inverts Hdm2.


Module V2.
Section V2.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv3_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2.
End V2.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB1RD_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ B C [1;1] [0;1] 8 143 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM8.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ B C [1;1] [0;1] 8 143 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM14.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ B C [1;1] [0;1] 8 143 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM15.

Module TM36.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ C A [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM36.

Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ C A [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM43.

Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM55.

Module TM56.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM56.

Module TM68.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LD_1RE0RA_1RF---_1RC1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D A [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM68.

Module TM69.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LD_1RD0LF_1LE1RF_1LC0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ F D [0;1] [0;1] 8 143 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM69.

Module TM70.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM70.

Module TM71.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RD_1RD0LF_1LE1RF_1LC0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ F D [0;1] [0;1] 8 143 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM71.

Module TM72.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LD_1RE0RA_1RF---_1RC0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D A [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM72.

Module TM73.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM73.


Module V2a.
Section V2a.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+2) |> [0;0;0] *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [1;0;0;0] *> r.

Hypothesis ROv'_0:
 forall l n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1] *> rd0 *> rd1 *> 0inf.

Hypothesis ROv'_1:
 forall l n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld1 <* ld0^^(n*5+4) |> rd0 *> rd1 *> 0inf.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv3_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+2)) (((k*2+1)*2^(lenR*5+2)-1)) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 0 -->+
  LC (lenL+1+(lenR*5+2)) (((k*2+1)*2^(lenR*5+2)-1)) |> RC 0.
Proof.
  epose proof (ROv4_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+1)) ((k*2+1)*2^(lenR*5+1)-1) |> RC1 1 2 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 2.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC4_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2a.
End V2a.


Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM40.

Module TM41.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [0;1] [0;1] 8 119 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM41.

Module TM44.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM44.

Module TM45.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [0;1] [0;1] 8 119 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM45.

Module V2aa.
Section V2aa.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+2) |> [0;0;0] *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [1;0;0;0] *> r.

Hypothesis ROv':
 forall l r n,
  l |> rd1^^n *> [1;0;0;0;1;1] *> r -->+
  l <| [0] *> rd0^^(1+n) *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv3_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+2)) (((k*2+1)*2^(lenR*5+2)-1)) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 0 -->+
  LC (lenL+1+(lenR*5+2)) (((k*2+1)*2^(lenR*5+2)-1)) |> RC 0.
Proof.
  epose proof (ROv4_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov l lenR:
  l |> RC' (lenR) 0 -->+
  l <| RC 0.
Proof.
  unfold RC',RC.
  rw_Bin.
  follow10 ROv'.
  rewrite lpow_all0.
  2: solve_const0_eq.
  simpl_tape.
  finish.
Qed.

Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      eexists (cfgL _ _ _). split.
      1: follow10 corner_case; follow100 RC'_Ov; finish.
      spl.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC4_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2aa.
End V2aa.

Module TM46.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2aa.nonhalt _ C A [0;1] [0;1] 6 23 1).
  1-10: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM46.

Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2aa.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-10: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM47.

Module TM61.
Definition tm := Eval compute in (TM_from_str "1RB0RB_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM61.

Module TM62.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [0;1] [0;1] 8 119 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM62.

Module TM64.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [0;1] [0;1] 8 119 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM64.

Module TM65.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM65.

Module TM66.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2aa.nonhalt _ D B [0;1] [0;1] 5 19 1).
  1-10: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM66.


Module V3.
Section V3.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis LOv_0:
 forall r n,
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0;0;0] *> r.

Hypothesis LOv_1:
 forall r n m,
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^3 |> rd0^^m *> rd1 *> r.

Hypothesis ROv4_0_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1 |> [0;0;0;0] *> r.

Hypothesis ROv4_0_1:
 forall l r n m,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+3) <* ld1^^3 |> rd0^^m *> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+6) |> r.


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

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma LC_Ov_0 lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC4 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL n:
  LC lenL O <| RC (n*2+1) -->+
  LC (lenL+1+1+1) ((2^lenL-1)*2*2*2) |> RC (n+1).
Proof.
  lowbitS_cases n.
  rewrite Nat.sub_add by lia.
  solve_rule LOv_1.
Qed.

Lemma RC4_Ov_0_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 ((m*2+1)*2^i*2) -->+
  LC (lenL+1+(lenR*5+3)+1) (((k*2+1)*2^(lenR*5+3)-1)*2) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_0_0.
Qed.

Lemma RC4_Ov_0_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 (0*2) -->+
  LC (lenL+1+(lenR*5+3)+1) (((k*2+1)*2^(lenR*5+3)-1)*2) |> RC 0.
Proof.
  epose proof (ROv4_0_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 (m*2+1) -->+
  LC (lenL+1+(lenR*5+3)+1+1+1) (((k*2+1)*2^(lenR*5+3)-1)*2*2*2) |> RC (m+1).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv4_0_1.
Qed.

Lemma RC4_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+6)) (((k*2+1)*2^(lenR*5+6)-1)) |> RC m.
Proof.
  solve_rule ROv4_1.
Qed.



Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    divmod2_cases n.
    + lowbit_cases n'.
      1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: apply LC_Ov_0; lia.
      pose proof (split_bound_v2 x i).
      spl.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Ov_1; lia.
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * lowbit_cases n'0.
        {
          eexists (cfgR _ _ _). split.
          1: apply RC4_Ov_0_0_0; lia.
          solve_v1 k lenL (n'*5).
        }
        {
          eexists (cfgR4 _ _ _ _ _). split.
          1: apply RC4_Ov_0_0; lia.
          solve_v1 k lenL (n'*5).
        }
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_0_1; lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_1; lia.
      solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V3.
End V3.

Module TM74.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_1LA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM74.

Module TM75.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1RD1LC_1LB1RF_1LD0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C D [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 8 174 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM75.

Module TM76.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC---_1RD0LF_1RE1LD_1LC1RA_1LE0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D E [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 6 37 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM76.

Module TM77.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC1RE_1RD0LA_1RB1LD_1RF0RB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 3 1 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM77.

Module TM80.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LF_1RA1LC_1RE0RA_1RB---_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM80.

Module TM81.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC1LB_1LA1RE_0RC0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ B C [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 7 46 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM81.

Module TM82.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RA0LD_0RB0LD_1RF0RB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ A B [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 3 1 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM82.

Module TM83.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_1RD1LC_1LB1RF_0RD0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C D [1;1;1;0;0;0;0] [1;1;1;1;1;0;1] 5 25 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM83.


Module V2b.
Section V2b.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [0;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd1 *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC (m*2+1).
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2b.
End V2b.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 4 9 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM9.

Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB0LE_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 4 9 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM19.

Module TM22.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC---_1RD1LD_1RE1LD_1LF1RA_1LC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ D E [1;1] [0;1] 3 1 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM22.

Module TM23.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1LA_1RF0RB_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ A B [1;1] [0;1] 4 9 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM23.

Module TM24.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LC_1RD1LC_1LA1RE_1RF0RD_1RB---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C D [1;1] [0;1] 5 19 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM24.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB1LB_1RC1LB_1LD1RE_1LA0LD_1RF0RC_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 6 23 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM25.


Module V2ba.
Section V2ba.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [0;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd1 *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5) |> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5+3) |> [0;0;0;0] *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0 <* ld1 <* ld0^^(n*5+1) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0 <* ld1 <* ld0^^(n*5+3) |> [1] *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC (m*2+1).
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+1+(lenR*5+1)) (((k*2+1)*2+1)*2^(lenR*5+1)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2ba.
End V2ba.

Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1LD_1RF0RB_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ba.nonhalt _ A B [1;1;1;1] [0;1;0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM29.

Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC---_1RD1LC_1RE1LD_1LF1RA_1LC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ba.nonhalt _ D E [1;1;1;1] [0;1;0;1] 8 151 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM30.

Module TM31.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1RD1LC_1LE1RF_1LB0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ba.nonhalt _ C D [1;1;1;1] [0;1;0;1] 6 23 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM31.

Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD1LC_1RA1LD_1RF0RA_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ba.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 2 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM32.


Module V2d.
Section V2d.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.

Hypothesis ROv4_0:
 forall l r n m,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd0^^(1+m) *> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [1] *> rd0^^(1+m) *> rd1 *> r.

Hypothesis ROv'_0:
 forall l n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld1 <* ld0^^(n*5+2) |> rd0 *> rd1 *> 0inf.

Hypothesis ROv'_1:
 forall l n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> 0inf -->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> rd0 *> rd1 *> 0inf.


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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv3_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+(lenR*5+1)) (((k*2+1)*2^(lenR*5+1)-1)) |> RC ((m+1)*2).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 2.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC1 1 2 0.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbitS_cases m.
      eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply RC4_Ov_1; lia.
      solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2d.
End V2d.

Module TM37.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [0;1] [0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM37.

Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [0;1] [0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM39.

Module TM54.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [0;1] [0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM54.

Module TM63.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [0;1] [0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM63.


Module V2da.
Section V2da.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [1;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0] *> r.

Hypothesis ROv4_0:
 forall l r n m,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> rd0^^m *> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1;0;0] *> r-->+
  l <* ld1 <* ld0^^(n*5+3) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1;0;0] *> r-->+
  l <* ld1 <* ld0^^(n*5+5) |> [1] *> r.


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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv3_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+(lenR*5+1)) (((k*2+1)*2^(lenR*5+1)-1)) |> RC ((m+1)*2+1).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.


Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  unfold RC'.
  epose proof (ROv'_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+5)) ((k*2+1)*2^(lenR*5+5)-1) |> RC 1.
Proof.
  unfold RC'.
  epose proof (ROv'_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbitS_cases m.
      eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbitS_cases m.
      eexists (cfgR4 _ _ _ _ _). split.
      1: apply RC4_Ov_1; lia.
      solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2da.
End V2da.

Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2da.nonhalt _ D B [0;1] [0;1] 3 2 3).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM48.

Module TM49.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LA_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2da.nonhalt _ C A [0;1] [0;1] 6 39 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM49.

Module TM57.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF0RA_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2da.nonhalt _ C A [0;1] [0;1] 6 39 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM57.

Module TM58.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2da.nonhalt _ D B [0;1] [0;1] 3 2 3).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM58.

Module V2bb.
Section V2bb.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5) |> [0;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5+2) |> rd1 *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5) |> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5+3) |> [0;0;0;0] *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0 <* ld1 <* ld0^^(n*5+1) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0 <* ld1 <* ld0^^(n*5+3) |> [1] *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC 0.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+1+(lenR*5+2)) (((k*2+1)*2+1)*2^(lenR*5+2)-1) |> RC (m*2+1).
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+1+(lenR*5+1)) (((k*2+1)*2+1)*2^(lenR*5+1)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+1+(lenR*5+3)) (((k*2+1)*2+1)*2^(lenR*5+3)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2bb.
End V2bb.

Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_0LD0LC_1RE0RB_1RF---_1RA1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2bb.nonhalt _ A B [1;1;1;1] [0;1;0;1] 5 21 1).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM50.

Module TM51.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RF1LF_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2bb.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 2 2).
  1-11: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM51.

Module V2bc.
Section V2bc.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis tr:Q*Sym.
Hypothesis lenL0 k0 n0:nat.

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

Hypothesis ROv1_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.

Hypothesis ROv1_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5+2) |> [0;0;0] *> r.

Hypothesis ROv3_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*5) |> [0;0;0;0] *> r.

Hypothesis ROv3_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd1 *> r.

Hypothesis ROv4_0:
 forall l r n,
  l |> rd1^^0 *> [1;0;0;0;1;0;0;0;0] *> rd1^^n *> rd0 *> r -->+
  l <* ld1 <* ld0 |> rd0^^(1+n) *> rd1 *> r.

Hypothesis ROv4_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0^^2 <* ld1 <* ld0^^(n*5+2) |> [0;0;0;0] *> r.

Hypothesis ROv4_2:
 forall l r n,
  l |> rd1^^(n*2+2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld0^^2 <* ld1 <* ld0^^(n*5+4) |> rd1 *> r.

Hypothesis ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0^^2 <* ld1 <* ld0^^(n*5) |> r.

Hypothesis ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld0^^2 <* ld1 <* ld0^^(n*5+2) |> [1] *> r.



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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+(lenR*5+2)) (((k*2+1)*2+1)*2^(lenR*5+2)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+1+(lenR*5+2)) (((k*2+1)*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+1+lenR*5) ((((k*2+1)*2+1)*2^(lenR*5)-1)) |> RC 0.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC (m*2+1).
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k m:
  k<2^lenL ->
  LC lenL k |> RC4 0 0 m -->+
  LC (lenL+1+1) ((((k*2)*2+1))) |> RC ((m+1)*2).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+1+(lenR*5+2)) ((((k*2+1)*2+1)*2+1)*2^(lenR*5+2)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+1+1+(lenR*5+2)) ((((k*2+1)*2+1)*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC4_Ov_2 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+2) 0 m -->+
  LC (lenL+1+1+1+(lenR*5+4)) (((((k*2+1)*2+1)*2+1)*2^(lenR*5+4)-1)) |> RC (m*2+1).
Proof.
  solve_rule ROv4_2.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+1+1+(lenR*5)) ((((k*2+1)*2+1)*2+1)*2^(lenR*5)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+1+1+(lenR*5+2)) ((((k*2+1)*2+1)*2+1)*2^(lenR*5+2)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + destruct n'.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_0; lia.
        spl.
      * replace (S n'*2) with (n'*2+2) by lia.
        eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_2; lia.
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Notation x0 := (cfgL lenL0 k0 n0).
Hypothesis init: c0 -->* to_config x0.
Hypothesis Pinit: P x0.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_cond with (P:=P).
  2: apply Pinit.
  apply closed.
Qed.

End V2bc.
End V2bc.

Module TM20.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC---_1RD0LA_1RE1LD_1LF1RA_1LC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2bc.nonhalt _ D E [1;1;1;1;1;1] [0;1;0;1;0;1] 5 22 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM20.

Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LF_1RD1LC_1LE1RF_1LB0LE_1RA0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2bc.nonhalt _ C D [1;1;1;1;1;1] [0;1;0;1;0;1] 8 155 2).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM21.


Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1] *> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv3_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd0 *> r.
Proof.
  es.
Qed.

Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.
Proof.
  es.
Qed.

Lemma ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.
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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) (((k*2+1)*2^(lenR*5)-1)) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) (((k*2+1)*2^(lenR*5)-1)) |> RC 1.
Proof.
  epose proof (ROv3_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC (m*2).
Proof.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n+m*2<k)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        destruct n'.
        1: lia.
        replace (S n'*5) with (n'*5+5) by lia.
        solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 19 1)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  apply closed.
Qed.

End TM10.


Module TM11.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1] *> rd0^^(1+m) *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv3_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd0^^(1+m) *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.
Proof.
  es.
Qed.

Lemma ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.
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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+lenR*5) (((k*2+1)*2^(lenR*5)-1)) |> RC1 (i+1) ((2^(i+1)-1)*2) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC ((m+1)*2).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n+m*2<k)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbitS_cases m.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply RC3_Ov_0; lia.
      rw_pa.
      spl.
      pose proof (split_bound_v2 x i).
      destruct n'.
      1: lia.
      replace (S n'*5) with (n'*5+5) by lia.
      solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 119 1)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  apply closed.
Qed.

End TM11.


Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3_0 l r n m:
  l |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> [0;0;0;0] *> rd0^^m *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv3_1 l r n m:
  l |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> rd1 *> rd0^^m *> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.
Proof.
  es.
Qed.

Lemma ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.
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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+(lenR*5+1)) (((k*2+1)*2^(lenR*5+1)-1)) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_0.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC ((m+1)*2+1).
Proof.
  lowbitS_cases m.
  rewrite Nat.sub_add by lia.
  solve_rule ROv3_1.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbitS_cases m.
      eexists (cfgR4 _ _ _ _ _). split.
      1: apply RC3_Ov_0; lia.
      pose proof (split_bound_v2 x i).
      solve_v1 k lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 7 15 1)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  apply closed.
Qed.

End TM12.


Module TM18.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1LB_1LD1RE_1LB0LD_1RF0RC_1RA---").
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

Lemma ROv1_0 l r n:
  l |> rd1^^(n*2) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5) |> [1;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*2+1) *> [1;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+3) |> [0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3_0 l r k n:
  l <* ld0 <* ld1^^k |> rd1^^(n*2) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^k <* ld0^^(n*5+2) |> [0;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv3_1 l r k n:
  l <* ld0 <* ld1^^k |> rd1^^(n*2+1) *> [1;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^k <* ld0^^(n*5+4) |> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_0 l r n:
  l |> rd1^^(n*2) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+1) |> rd1 *> r.
Proof.
  es.
Qed.

Lemma ROv4_1 l r n:
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*5+4) |> [0;0;0;0] *> r.
Proof.
  es.
Qed.

Lemma ROv'_0:
 forall l r n,
  l |> rd1^^(n*2) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+2) |> r.
Proof.
  es.
Qed.

Lemma ROv'_1:
 forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;0;0;1;1] *> r-->+
  l <* ld1 <* ld0^^(n*5+4) |> [1] *> r.
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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC4_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC4 len (1+n) m -->+
  l <| RC4 len n m.
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

Lemma RC1_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC4 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*5) ((k*2+1)*2^(lenR*5)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC3 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+3)) ((k*2+1)*2^(lenR*5+3)-1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k+1<2^lenL ->
  LC lenL (k+1) |> RC3 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+(lenR*5+2)) (((k+1)*2^(lenR*5+2)-1)) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  lowbitS_cases k.
  rewrite Nat.sub_add by lia.
  intros H.
  rewrite (lowbit_split _ _ _ H).
  pose proof (lowbit_split_lt _ _ _ H).
  remember (lenL-i0-1) as v1.
  unfold LC,RC3,RC4,RC.
  rewrite <-Nat.mul_assoc.
  rewrite <-Nat.pow_add_r.
  remember (i0+(lenR*5+2)) as v2.
  replace (v1+1+i0+(lenR*5+2)) with (v1+1+v2) by lia.
  rw_Bin.
  all: solve_pow2_lt.
  follow10 ROv3_0.
  replace v2 with ((lenR*5+2)+i0) by lia.
  simpl_tape.
  simpl_rotate.
  finish.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k+1<2^lenL ->
  LC lenL (k+1) |> RC3 (lenR*2) 0 0 -->+
  LC (lenL+(lenR*5+2)) (((k+1)*2^(lenR*5+2)-1)) |> RC 0.
Proof.
  lowbitS_cases k.
  rewrite Nat.sub_add by lia.
  intros H.
  rewrite (lowbit_split _ _ _ H).
  pose proof (lowbit_split_lt _ _ _ H).
  remember (lenL-i-1) as v1.
  unfold LC,RC3,RC4,RC.
  rewrite <-Nat.mul_assoc.
  rewrite <-Nat.pow_add_r.
  remember (i+(lenR*5+2)) as v2.
  replace (v1+1+i+(lenR*5+2)) with (v1+1+v2) by lia.
  rw_Bin.
  all: solve_pow2_lt.
  follow10 ROv3_0.
  replace v2 with ((lenR*5+2)+i) by lia.
  simpl_tape.
  simpl_rotate.
  finish.
Qed.

Lemma RC3_Ov_1 lenL k lenR m:
  k+1<2^lenL ->
  LC lenL (k+1) |> RC3 (lenR*2+1) 0 m -->+
  LC (lenL+(lenR*5+4)) ((k+1)*2^(lenR*5+4)-1) |> RC (m*2+1).
Proof.
  lowbitS_cases k.
  rewrite Nat.sub_add by lia.
  intros H.
  rewrite (lowbit_split _ _ _ H).
  pose proof (lowbit_split_lt _ _ _ H).
  remember (lenL-i-1) as v1.
  unfold LC,RC3,RC4,RC.
  rewrite <-Nat.mul_assoc.
  rewrite <-Nat.pow_add_r.
  remember (i+(lenR*5+4)) as v2.
  replace (v1+1+i+(lenR*5+4)) with (v1+1+v2) by lia.
  rw_Bin.
  all: solve_pow2_lt.
  follow10 ROv3_1.
  replace v2 with ((lenR*5+4)+i) by lia.
  simpl_tape.
  simpl_rotate.
  finish.
Qed.

Lemma RC4_Ov_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2) 0 m -->+
  LC (lenL+1+lenR*5+1) (((k*2+1)*2^(lenR*5)-1)*2+1) |> RC (m*2+1).
Proof.
  solve_rule ROv4_0.
Qed.

Lemma RC4_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC4 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv4_1.
Qed.

Lemma RC4_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC4 (lenR*2+1) 0 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 0.
Proof.
  epose proof (ROv4_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Incs lenL k lenR n m:
  k<2^lenL ->
  n+k+1<2^(lenR+1) ->
  LC lenL k |> RC1 lenR (n+k+1) m -->*
  LC lenL 0 <| RC1 lenR n m.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia.
    follow100 RC1_Inc.
    finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow100 RC1_Inc.
    follow100 LC_Inc.
    follow IHk.
    1,2: lia.
    finish.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0;0] len n ([0;0;0;1;1]*>0inf).

Lemma LC_Ov' lenL lenR:
  LC lenL 0 <| RC1 (lenR+1) (((0*2+1)*2^lenR-1)*2) 0 -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC' lenR ((2^lenR-1)*2).
Proof.
  rewrite Nat.add_comm.
  unfold LC,RC1,RC',RC.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv.
  cbn; simpl_rotate.
  epose proof (ROv1_0 _ _ 0) as I1.
  follow100 I1. clear I1.
  simpl_rotate.
  simpl_tape.
  finish.
Qed.

Lemma RC'_Inc len n l:
  1+n<2^(len+1) ->
  l |> RC' len (1+n) -->+
  l <| RC' len n.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  gen k.
  induction n; intros.
  - finish.
  - follow100 RC'_Inc.
    rewrite Nat.add_succ_r.
    follow100 LC_Inc.
    follow IHn.
    1,2: lia.
    finish.
Qed.

Lemma RC'_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2) 0 -->+
  LC (lenL+1+(lenR*5+2)) ((k*2+1)*2^(lenR*5+2)-1) |> RC 0.
Proof.
  unfold RC'.
  solve_rule ROv'_0.
Qed.

Lemma RC'_Ov_1 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' (lenR*2+1) 0 -->+
  LC (lenL+1+(lenR*5+4)) ((k*2+1)*2^(lenR*5+4)-1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'_1.
Qed.


Ltac lia' := rw_pa; lia.

Lemma corner_case lenL:
  LC (lenL+1) O <| RC (2^(lenL+1)) -->+
  LC (lenL + 1 + 1) (2 ^ lenL * 2) |> RC' lenL 0.
Proof.
  replace (2^(lenL+1)) with ((0*2+1)*2^(lenL+1)) by lia'.
  follow10 LC_Ov.
  replace ((2^(lenL+1)-1)*2) with (((0*2+1)*2^(lenL)-1)*2+(2^(lenL+1)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  follow100 LC_Ov'.
  replace ((2^(lenL+1)-1)*2) with (2^lenL*2+(2^lenL-1)*2) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  finish.
Qed.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
| cfgR4(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
| cfgR4 lenL k lenR n m => LC lenL k |> RC4 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR1 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k lenR n m => lenL>=1 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR4 lenL k lenR n m => lenL>=1 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k.
    2: {
      eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      spl.
    }
    destruct (Nat.eqb_spec n (2^lenL)).
    + subst.
      remember (lenL-1) as lenL'.
      replace lenL with (lenL'+1) in * by lia.
      divmod2_cases lenL'.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_0.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
      * eexists (cfgR _ _ _). split.
        1: follow10 corner_case.
        1: follow100 RC'_Ov_1.
        1: solve_pow2_lt.
        1: finish.
        spl.
        rw_pa.
        remember (n'*2).
        remember (n'*5).
        zify_pow2sub1; lia.
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      pose proof (split_bound_v3 x i lenL).
      spl.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    spl.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR3 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        solve_v1 k lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      spl.
    }
    remember (k-1) as k'.
    replace k with (k'+1) in * by lia.
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        solve_v1 (k'+1) lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC3_Ov_0; lia.
        pose proof (split_bound_v2 x i).
        solve_v1 (k'+1) lenL (n'*5).
    + eexists (cfgR _ _ _). split.
      1: apply RC3_Ov_1; lia.
      solve_v1 (k'+1) lenL (n'*5).
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR4 _ _ _ _ _). split.
      1: follow10 RC4_Inc; follow100 LC_Inc; finish.
      spl.
    }
    divmod2_cases lenR.
    + eexists (cfgR _ _ _). split.
      1: apply RC4_Ov_0; lia.
      solve_v1 k lenL (n'*5).
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC4_Ov_1_0; lia.
        solve_v1 k lenL (n'*5).
      * eexists (cfgR4 _ _ _ _ _). split.
        1: apply RC4_Ov_1; lia.
        solve_v1 k lenL (n'*5).
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 8 143 2)).
  1: esx.
  eapply progress_nonhalt_cond with (P:=P).
  2: cbn; lia.
  apply closed.
Qed.

End TM18.


