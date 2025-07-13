From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Notation rm1 := [1;1;0;0].
Notation rm2 := [1;0;1;0;0].

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

Module V3.
Section V3.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
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
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.

Hypothesis ROv1_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.

Hypothesis ROv2_0:
  forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [0] *> r.

Hypothesis ROv2_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> r.

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

Lemma RC2_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC2 len (1+n) m -->+
  l <| RC2 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC1_Ov_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3+1) (((k*2+1)*2^(lenR*3)-1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_0.
Qed.

Lemma RC2_Ov_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3+1) (((k*2+1)*2^(lenR*3)-1)*2+1) |> RC 0.
Proof.
  epose proof (ROv2_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_1.
Qed.

Lemma RC2_Ov_1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 0 -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC 1.
Proof.
  epose proof (ROv2_1 _ 0inf _) as I1.
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
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      spl.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        rw_pa.
        spl.
        destruct n'.
        1: lia.
        replace (S n'*3) with (n'*3+3) by lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        spl.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      rw_pa.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_0; lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        spl.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC2_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_1_0; lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        spl.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
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


Module TM29.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LE---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [0;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM29.

Module TM32.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [0;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM32.

Module TM41.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1LC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [0;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM41.

Module TM95.
Definition tm := Eval compute in (TM_from_str "1RB1LC_0LA---_1LD0LC_1RE0RA_1LC1RF_1RD0RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D E [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM95.

Module TM116.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RC0RA_0RF1LB_0LA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM116.

Module TM152.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RC0RA_0RF0LD_0LB---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM152.

Module TM163.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LA0LC_1RA0RB_1RF0LD_0LE---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ A B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM163.

Module TM184.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1LC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ A B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM184.

Module TM187.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ A B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM187.

Module TM189.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_1LD0LC_1RB1LD_1RA0RB_1LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM189.

Module V3a.
Section V3a.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
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
  l |> rd1^^(n*2) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> [1;0] *> r.

Hypothesis ROv1_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.

Hypothesis ROv2_0:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) |> [0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv2_1:
  forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [1;0] *> rd0^^m *> rd1 *> r.

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

Lemma RC2_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC2 len (1+n) m -->+
  l <| RC2 len n m.
Proof.
  intros H.
  apply RBinDec2_spec; try lia.
  follow' RInc.
Qed.

Lemma RC1_Ov_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv1_0.
Qed.

Lemma RC1_Ov_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 0 -->+
  LC (lenL+1+lenR*3) ((k*2+1)*2^(lenR*3)-1) |> RC 1.
Proof.
  epose proof (ROv1_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC1_Ov_1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv1_1.
Qed.

Lemma RC1_Ov_1_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 0 -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC 0.
Proof.
  epose proof (ROv1_1 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+lenR*3+1) (((k*2+1)*2^(lenR*3)-1)*2+1) |> RC1 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_0.
Qed.

Lemma RC2_Ov_1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_1.
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
| cfgR1(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      spl.
      pose proof (split_bound_v1 x i lenL).
      lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0_0; lia.
        rw_pa.
        spl.
        destruct n'.
        1: lia.
        replace (S n'*3) with (n'*3+3) by lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_1_0; lia.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        spl.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC1_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      rw_pa.
      lia.
    }
    divmod2_cases lenR.
    + lowbitS_cases m.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC2_Ov_0; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
    + lowbitS_cases m.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_1; lia.
        rw_pa.
        spl.
        pose proof (split_bound_v2 x i).
        zify_le_mul_r; lia.
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

End V3a.
End V3a.


Module TM25.
Definition tm := Eval compute in (TM_from_str "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3a.nonhalt _ D B [0;1] [0;1] 5 17 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM25.

Module TM154.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_1LD0LC_1RB1RF_1RD0RB_0RA0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3a.nonhalt _ D B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM154.

Module TM188.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RE---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3a.nonhalt _ A B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM188.

Module TM190.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB1RF_0RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3a.nonhalt _ A B [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM190.


Module V5.
Import List BinDigits.
Section V5.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
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
  forall r n m,
  ldh <* ld1^^n <| rd1^^(m*2) *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld1<+ld0<+ld0)^^m <* ld1 <* ld0 |> r.

Definition LOv_0_ls m :=
  <[D1;D0;D0]^^m <+ <[D1;D0].

Lemma LC_Ov_0 lenL i m:
  let ls := LOv_0_ls i in
  LC lenL 0 <| RC ((m*2+1)*2^(i*2)-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_0_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv_0.
Qed.

Hypothesis LOv_1:
  forall r n m,
  ldh <* ld1^^n <| rd1^^(m*2+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld1<+ld0<+ld0)^^(m+1) |> [0] *> r.

Definition LOv_1_ls m :=
  <[D1;D0;D0]^^(m+1).

Lemma LC_Ov_1 lenL i0 i m:
  let ls := LOv_1_ls i in
  LC lenL 0 <| RC (((m*2+1)*2^i0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv_1.
Qed.

Lemma LC_Ov_1_0 lenL i:
  let ls := LOv_1_ls i in
  LC lenL 0 <| RC ((0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv_1.
Qed.

Hypothesis ROv1_0_0_0:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;1;0;0] *> rd0 *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) <* (ld0<+ld1<+ld0)^^(m+1) |> r.

Definition ROv1_0_0_0_ls n m :=
  [D1] <+ [D0]^^(n*3+1) <+ <[D0;D1;D0]^^(m+1).

Lemma RC1_Ov_0_0_0 lenL k lenR i m:
  let ls := ROv1_0_0_0_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 (((m*2+1)*2^(i*2)-1)*2) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_0_0_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_0_0.
Qed.

Hypothesis ROv1_0_0_1:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;1;0;0] *> rd0 *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) <* (ld1<+ld0<+ld0)^^(m+1) |> [0] *> r.

Definition ROv1_0_0_1_ls n m :=
  [D1] <+ [D0]^^(n*3+2) <+ <[D1;D0;D0]^^(m+1).

Lemma RC1_Ov_0_0_1 lenL k lenR i0 i m:
  let ls := ROv1_0_0_1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((((m*2+1)*2^i0*2+1)*2^(i*2+1)-1)*2) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_0_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_0_1.
Qed.

Lemma RC1_Ov_0_0_1_0 lenL k lenR i:
  let ls := ROv1_0_0_1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 (((0*2+1)*2^(i*2+1)-1)*2) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_0_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_0_1.
Qed.

Hypothesis ROv1_0_10_0:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;1;0;0] *> rd1 *> rd0 *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) <* ld1 <* (ld0<+ld1<+ld0)^^m <* ld0 |> [0] *> r.

Definition ROv1_0_10_0_ls n m :=
  [D1] <+ [D0]^^(n*3+3) <+ [D1] <+ <[D0;D1;D0]^^m <+ [D0].

Lemma RC1_Ov_0_10_0 lenL k lenR i0 i m:
  let ls := ROv1_0_10_0_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((((m*2+1)*2^i0*2+1)*2^(i*2)-1)*2*2+1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_10_0_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_10_0.
Qed.

Lemma RC1_Ov_0_10_0_0 lenL k lenR i:
  let ls := ROv1_0_10_0_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 (((0*2+1)*2^(i*2)-1)*2*2+1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_10_0_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_10_0.
Qed.

Hypothesis ROv1_0_10_1:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;1;0;0] *> rd1 *> rd0 *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) <* ld1 <* (ld0<+ld1<+ld0)^^(m+1) |> r.

Definition ROv1_0_10_1_ls n m :=
  [D1] <+ [D0]^^(n*3+3) <+ [D1] <+ <[D0;D1;D0]^^(m+1).

Lemma RC1_Ov_0_10_1 lenL k lenR i m:
  let ls := ROv1_0_10_1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 (((m*2+1)*2^(i*2+1)-1)*2*2+1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_10_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_10_1.
Qed.

Hypothesis ROv1_0_11:
  forall l r n,
  l |> rd1^^(n*2) *> [1;1;0;0] *> rd1^^2 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> r.

Definition ROv1_0_11_ls n :=
  [D1] <+ [D0]^^(n*3+4).

Lemma RC1_Ov_0_11 lenL k lenR m:
  let ls := ROv1_0_11_ls lenR in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2) 0 ((m*2+1)*2+1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_0_11_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_0_11.
Qed.

Hypothesis ROv1_1_0:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) |> r.

Definition ROv1_1_0_ls n :=
  [D1] <+ [D0]^^(n*3+4).

Lemma RC1_Ov_1_0 lenL k lenR m:
  let ls := ROv1_1_0_ls lenR in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 (m*2) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_1_0_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_1_0.
Qed.

Hypothesis ROv1_1_1:
  forall l r n m,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+5) <* (ld1<+ld0<+ld0)^^m |> [0] *> r.

Definition ROv1_1_1_ls n m :=
  [D1] <+ [D0]^^(n*3+5) <+ <[D1;D0;D0]^^m.

Lemma RC1_Ov_1_1 lenL k lenR i0 i m:
  let ls := ROv1_1_1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 (((m*2+1)*2^i0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_1_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_1_1.
Qed.

Lemma RC1_Ov_1_1_0 lenL k lenR i:
  let ls := ROv1_1_1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((0*2+1)*2^(i*2+1)-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_1_1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_1_1.
Qed.

Hypothesis ROv1_1_2:
  forall l r n m,
  l |> rd1^^(n*2+1) *> [1;1;0;0] *> rd1^^(m*2+2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) <* (ld0<+ld1<+ld0)^^(m+1) |> r.

Definition ROv1_1_2_ls n m :=
  [D1] <+ [D0]^^(n*3+4) <+ <[D0;D1;D0]^^(m+1).

Lemma RC1_Ov_1_2 lenL k lenR i m:
  let ls := ROv1_1_2_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 (lenR*2+1) 0 ((m*2+1)*2^(i*2+2)-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_1_2_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1_1_2.
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


Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL*2 /\ k<2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL*2 /\ k<2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac solve_v1 k lenL x :=
  pose proof (val_spec x);
  remember (length x) as v1;
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^v1));
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
  - destruct k as [|k].
    + lowbitS_cases n.
      divmod2_cases i.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        pose proof (val_spec (LOv_0_ls n')).
        rw_pa.
        spl.
        -- zify_pow2sub1; lia.
        -- zify_pow2sub1.
           zify_le_mul_r; lia.
        -- zify_pow2sub1; lia.
      * lowbit_cases x.
        -- eexists (cfgR _ _ _). split.
           1: apply LC_Ov_1_0.
           pose proof (val_spec (LOv_1_ls n')).
           rw_pa.
           spl.
           ++ zify_pow2sub1; lia.
           ++ zify_pow2sub1; lia.
           ++ zify_pow2sub1; lia.
        -- eexists (cfgR1 _ _ _ _ _). split.
           1: apply LC_Ov_1.
           pose proof (val_spec (LOv_1_ls n')).
           rw_pa.
           spl.
           pose proof (split_bound_v1 x0 i lenL).
           zify_le_mul_r; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * lowbitS_cases n'0.
        divmod2_cases i.
        {
          eexists (cfgR _ _ _). split.
          1: apply RC1_Ov_0_0_0; lia.
          solve_v1 k lenL (ROv1_0_0_0_ls n' n'0).
        }
        {
          lowbit_cases x.
          {
            eexists (cfgR _ _ _). split.
            1: apply RC1_Ov_0_0_1_0; lia.
            solve_v1 k lenL (ROv1_0_0_1_ls n' n'0).
          }
          {
            eexists (cfgR1 _ _ _ _ _). split.
            1: apply RC1_Ov_0_0_1; lia.
            solve_v1 k lenL (ROv1_0_0_1_ls n' n'0).
          }
        }
      * divmod2_cases n'0.
        {
          lowbitS_cases n'1.
          divmod2_cases i.
          {
            lowbit_cases x.
            {
              eexists (cfgR _ _ _). split.
              1: apply RC1_Ov_0_10_0_0; lia.
              solve_v1 k lenL (ROv1_0_10_0_ls n' n'0).
            }
            {
              eexists (cfgR1 _ _ _ _ _). split.
              1: apply RC1_Ov_0_10_0; lia.
              solve_v1 k lenL (ROv1_0_10_0_ls n' n'0).
            }
          }
          {
            eexists (cfgR _ _ _). split.
            1: apply RC1_Ov_0_10_1; lia.
            solve_v1 k lenL (ROv1_0_10_1_ls n' n'0).
          }
        }
        {
          eexists (cfgR _ _ _). split.
          1: apply RC1_Ov_0_11; lia.
          solve_v1 k lenL (ROv1_0_11_ls n').
        }
    + lowbitS_cases m.
      divmod2_cases i.
      * destruct n'0.
        {
          replace ((x*2+1)*2^(0*2)-1) with (x*2) by lia.
          eexists (cfgR _ _ _). split.
          1: apply RC1_Ov_1_0; lia.
          solve_v1 k lenL (ROv1_1_0_ls n').
        }
        {
          replace (S n'0*2) with (n'0*2+2) in * by lia.
          eexists (cfgR _ _ _). split.
          1: apply RC1_Ov_1_2; lia.
          solve_v1 k lenL (ROv1_1_2_ls n' n'0).
        }
      * lowbit_cases x.
        {
          eexists (cfgR _ _ _). split.
          1: apply RC1_Ov_1_1_0; lia.
          solve_v1 k lenL (ROv1_1_1_ls n' n'0).
        }
        {
          eexists (cfgR1 _ _ _ _ _). split.
          1: apply RC1_Ov_1_1; lia.
          pose proof (split_bound_v2 x0 i).
          solve_v1 k lenL (ROv1_1_1_ls n' n'0).
        }
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

End V5.
End V5.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LB_1LF1RD_1RE0RC_1RC---_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 2 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM3.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RF_1RD0LC_1LE1RC_1RB1LE_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ E B [1;1;1;0;0] [1;1;1;0;1] 3 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC---_1LD1RA_1RE0LD_1LF1RD_1RC1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ F C [1;1;1;0;0] [1;1;1;0;1] 3 5 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1RB_1RA1LD_1RF0RA_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ D A [1;1;1;0;0] [1;1;1;0;1] 2 1 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM6.

Module TM52.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_1LE1RD_1RC---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 2 1 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM52.

Module TM53.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RF_1RD1LC_1LA1RE_1RC0RD_1RB---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 3 5 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM53.

Module TM54.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RF_1RA0RB_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 3 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM54.

Module TM55.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 2 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM55.

Module TM56.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1LD1RF_1RA1LD_1RD0RA_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ D A [1;1;1;0;0] [1;1;1;0;1] 2 1 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM56.

Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RA_1RD1LC_1LF1RE_1RC0RD_0LB0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 3 5 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM57.

Module TM227.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RA_1RE0RD_---1LB_1LA1RF_1RC0RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ C E [1;1;1;0;0] [1;1;1;0;1] 3 5 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM227.

Module TM228.
Definition tm := Eval compute in (TM_from_str "1RB0RE_1LC1RF_1RD0LC_1LA1RC_---1LD_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 3 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM228.

Module TM229.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_1LD1RB_1RA0RE_---1LC_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ D A [1;1;1;0;0] [1;1;1;0;1] 2 1 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM229.

Module TM230.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0RF_1LE1RD_1RB0RC_1RA0LE_---1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 2 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM230.

Module TM231.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0RE_1LD1RA_1RF0LE_---1LF_1LB1RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 3 5 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM231.

Module TM232.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LE_1LD1RB_1RA0RE_---1LC_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ D A [1;1;1;0;0] [1;1;1;0;1] 2 1 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM232.

Module TM233.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0RF_1LE1RD_1RB0RC_1RA0LF_---1LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 2 3 1).
  1-12: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM233.


Module V6.
Import BinDigits.
Section V6.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
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
  ldh <* ld0^^n <* ld1 |> [0;0] *> r.

Lemma LC_Ov_0 lenL i m:
  LC lenL 0 <| RC ((m*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_0_0 lenL:
  LC lenL 0 <| RC (0*2) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC 0.
Proof.
  epose proof (LOv_0 0inf _) as I1.
  solve_rule I1.
Qed.

Hypothesis LOv_1:
  forall r n,
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^n <* ld1 |> [1;1] *> r.

Lemma LC_Ov_1 lenL m:
  LC lenL 0 <| RC (m*2+1) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> [1;1] *> RC m.
Proof.
  solve_rule LOv_1.
Qed.

Hypothesis ROv2_0_0:
  forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.

Lemma RC2_Ov_0_0 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (m*2) -->+
  LC (lenL+1+lenR*3+1+1+1) ((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)) |> RC m.
Proof.
  solve_rule ROv2_0_0.
Qed.

Hypothesis ROv2_0_1:
  forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1 *> r -->+
  l <* ld0 <* ld1^^(n*3+3) |> r.

Lemma RC2_Ov_0_1 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (m*2+1) -->+
  LC (lenL+1+lenR*3+1+1+1) ((((((k*2+1)*2^(lenR*3))*2)*2)*2)) |> RC m.
Proof.
  solve_rule ROv2_0_1.
Qed.

Hypothesis ROv2_1_00:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) <* ld1 |> [0;0] *> r.

Lemma RC2_Ov_1_00 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((m*2+1)*2^i*2*2) -->+
  LC (lenL+1+lenR*3+1+1+1+1+1) (((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_1_00.
Qed.

Lemma RC2_Ov_1_00_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 (0*2*2) -->+
  LC (lenL+1+lenR*3+1+1+1+1+1) (((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)*2+1)*2) |> RC 0.
Proof.
  epose proof (ROv2_1_00 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Hypothesis ROv2_1_01:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) <* ld1 |> [1;1] *> r.

Lemma RC2_Ov_1_01 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((m*2+1)*2) -->+
  LC (lenL+1+lenR*3+1+1+1+1+1) (((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)*2+1)*2) |> [1;1] *> RC m.
Proof.
  solve_rule ROv2_1_01.
Qed.

Hypothesis ROv2_1_10:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) <* ld1 |> [1;1] *> r.

Lemma RC2_Ov_1_10 lenL k lenR m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((m*2)*2+1) -->+
  LC (lenL+1+lenR*3+1+1+1+1+1) (((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)*2+1)*2) |> [1;1] *> RC m.
Proof.
  solve_rule ROv2_1_10.
Qed.

Hypothesis ROv2_1_11:
  forall l r n m,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+4) <* ld1 |> [0;0] *> rd0^^m *> rd1 *> r.

Lemma RC2_Ov_1_11 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 ((((m*2+1)*2^i-1)*2+1)*2+1) -->+
  LC (lenL+1+lenR*3+1+1+1+1+1) (((((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1)*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_1_11.
Qed.

Hypothesis ROv3_00:
  forall l r,
  l |> [1;1] *> rd0 *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1 |> [0;0] *> r.

Lemma RC3_00 lenL k i m:
  k<2^lenL ->
  LC lenL k |> [1;1] *> RC (((m*2+1)*2^i*2)*2) -->+
  LC (lenL+1+1+1) ((k*2*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_00.
Qed.

Lemma RC3_00_0 lenL k:
  k<2^lenL ->
  LC lenL k |> [1;1] *> RC ((0*2)*2) -->+
  LC (lenL+1+1+1) ((k*2*2+1)*2) |> RC 0.
Proof.
  epose proof (ROv3_00 _ 0inf) as I1.
  solve_rule I1.
Qed.

Hypothesis ROv3_01:
  forall l r,
  l |> [1;1] *> rd0 *> rd1 *> r -->+
  l <* ld1 <* ld0 <* ld1 |> [1;1] *> r.

Lemma RC3_01 lenL k m:
  k<2^lenL ->
  LC lenL k |> [1;1] *> RC ((m*2+1)*2) -->+
  LC (lenL+1+1+1) ((k*2*2+1)*2) |> [1;1] *> RC m.
Proof.
  solve_rule ROv3_01.
Qed.

Hypothesis ROv3_10:
  forall l r,
  l |> [1;1] *> rd1 *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1 |> [1;1] *> r.

Lemma RC3_10 lenL k m:
  k<2^lenL ->
  LC lenL k |> [1;1] *> RC ((m*2)*2+1) -->+
  LC (lenL+1+1+1) ((k*2*2+1)*2) |> [1;1] *> RC m.
Proof.
  solve_rule ROv3_10.
Qed.

Hypothesis ROv3_11:
  forall l r m,
  l |> [1;1] *> rd1^^(2+m) *> rd0 *> r -->+
  l <* ld1 <* ld0 <* ld1 |> [0;0] *> rd0^^m *> rd1 *> r.

Lemma RC3_11 lenL k i m:
  k<2^lenL ->
  LC lenL k |> [1;1] *> RC ((((m*2+1)*2^i-1)*2+1)*2+1) -->+
  LC (lenL+1+1+1) ((k*2*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv3_11.
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



Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR3(lenL k n:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR3 lenL k n => LC lenL k |> [1;1] *> RC n
end.

Close Scope sym.


Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL*2 /\ k<2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL*2 /\ k<2^lenL
| cfgR2 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR3 lenL k n => n<=k<2^lenL
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
  - destruct k as [|k].
    + divmod2_cases n.
      * lowbit_cases n'.
        {
          eexists (cfgR _ _ _). split.
          1: apply LC_Ov_0_0; lia.
          spl.
        }
        {
          eexists (cfgR2 _ _ _ _ _). split.
          1: apply LC_Ov_0; lia.
          pose proof (split_bound_v2 x i).
          spl.
        }
      * eexists (cfgR3 _ _ _). split.
        1: apply LC_Ov_1; lia.
        spl.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    1: apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_0; lia.
        solve_v1 k lenL (n'*3).
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_1; lia.
        solve_v1 k lenL (n'*3).
    + divmod2_cases m.
      * divmod2_cases n'0.
        {
          lowbit_cases n'1.
          {
            eexists (cfgR _ _ _). split.
            1: apply RC2_Ov_1_00_0; lia.
            solve_v1 k lenL (n'*3).
          }
          {
            eexists (cfgR2 _ _ _ _ _). split.
            1: apply RC2_Ov_1_00; lia.
            solve_v1 k lenL (n'*3).
          }
        }
        {
          eexists (cfgR3 _ _ _). split.
          1: apply RC2_Ov_1_01; lia.
          solve_v1 k lenL (n'*3).
        }
      * divmod2_cases n'0.
        {
          eexists (cfgR3 _ _ _). split.
          1: apply RC2_Ov_1_10; lia.
          solve_v1 k lenL (n'*3).
        }
        {
          lowbitS_cases n'1.
          eexists (cfgR2 _ _ _ _ _). split.
          1: apply RC2_Ov_1_11; lia.
          solve_v1 k lenL (n'*3).
        }
  - divmod2_cases n.
    + divmod2_cases n'.
      * lowbit_cases n'0. 
        {
          eexists (cfgR _ _ _). split.
          1: apply RC3_00_0; lia.
          spl.
        }
        {
          eexists (cfgR2 _ _ _ _ _). split.
          1: apply RC3_00; lia.
          pose proof (split_bound_v2 x i).
          spl.
        }
      * eexists (cfgR3 _ _ _). split.
        1: apply RC3_01; lia.
        spl.
    + divmod2_cases n'.
      * eexists (cfgR3 _ _ _). split.
        1: apply RC3_10; lia.
        spl.
      * lowbitS_cases n'0.
        eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC3_11; lia.
        pose proof (split_bound_v2 x i).
        spl.
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

End V6.
End V6.

Module TM138.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RF_1LA0LD_0RE0LD_1LC---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 4 2 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM138.

Module TM139.
Definition tm := Eval compute in (TM_from_str "1LB---_1LC0LF_1RD0RF_1LB1RE_1RC0RD_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 5 18 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM139.

Module TM140.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0RE_1LD1RA_1LB0LE_0RF0LE_1LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 6 23 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM140.

Module TM143.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC0RE_1LD1RA_1LB0LE_1RF0LE_0LA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 6 23 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM143.

Module TM144.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RE_1RC0RA_1RF0LE_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ C A [1;1;1;0;0] [1;1;1;0;1] 5 18 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM144.

Module TM145.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RF_1LA0LD_1RE0LD_0LF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 4 2 1).
  1-14: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM145.


