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
Definition RC2 len n m := BinDec2 [0;0] [1;0] [0] len n (rd1 *> BinInc rd1 m). 


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
  unfold LC,RC,RC2;
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

Module V1.
Section V1.
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
  l |> rd1^^n *> [0;0] *> r -->+
  l <| rd0^^n *> [1;0] *> r.

Hypothesis LOv_0:
  forall r n,
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0] *> r.

Hypothesis LOv_1:
  forall r n,
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld1 |> r.

Hypothesis ROv2_0_0:
  forall l r n,
  l |> rd1^^(n*2) *> rm2 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) <* ld1 |> [0;0] *> r.

Hypothesis ROv2_0_1:
  forall l r n,
  l |> rd1^^(n*2) *> rm2 *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) <* ld1 <* ld1 |> r.

Hypothesis ROv2_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> rm2 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.

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

Lemma RC2_Ov_0_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((m*2+1)*2^i*2) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2) |> RC 0.
Proof.
  epose proof (ROv2_0_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (m*2+1) -->+
  LC (lenL+1+lenR*3+1+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2*2) |> RC m.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 m -->+
  LC (lenL+1+lenR*3+1+1+1) (((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1) |> RC m.
Proof.
  solve_rule ROv2_1.
Qed.

Lemma LC_Ov_0 lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC2 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL n:
  LC lenL O <| RC (n*2+1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2) |> RC n.
Proof.
  solve_rule LOv_1.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL*2 /\ k<2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL*2 /\ k<2^lenL
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
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eexists (cfgR2 _ _ _ _ _). split.
        1: apply LC_Ov_0.
        spl.
        pose proof (split_bound_v1 x i lenL).
        lia.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_1.
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
      * lowbit_cases n'0.
        -- eexists (cfgR _ _ _). split.
           1: apply RC2_Ov_0_0_0; lia.
           spl.
           rw_pa.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
           lia.
        -- eexists (cfgR2 _ _ _ _ _). split.
           1: apply RC2_Ov_0_0; lia.
           spl.
           zify_le_mul_r; lia.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_1; lia.
        spl.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        remember (n'*3).
        zify_pow2sub1; lia.
    + eexists (cfgR _ _ _). split.
      1: apply RC2_Ov_1; lia.
      spl.
      rw_pa.
      pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
      remember (n'*3).
      zify_pow2sub1; lia.
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

End V1.
End V1.


Module TM47.
Definition tm := Eval compute in (TM_from_str "1LB1LC_0RA0LB_1RD0RE_1RE1LD_0RF1RC_0LA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D E [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM47.

Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RF_0LD---_1LE1LF_0RD0LE_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM48.

Module TM49.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LB_1LE1RD_1RB0RC_1RA0LE_0LB---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM49.

Module TM50.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_1LE1RD_0LE---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM50.

Module TM58.
Definition tm := Eval compute in (TM_from_str "1RB1RB_0LC---_1RD1LC_1LF1RE_1RC0RD_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM58.

Module TM59.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_1RD1RD_0LE---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM59.

Module TM60.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_0LF1RD_0LE---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM60.

Module TM61.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA0RF_1RA0RB_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM61.

Module TM62.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0LB_1LE0RD_0LC---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM62.

Module TM73.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_0LC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM73.

Module TM74.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LB_1LE1RD_0LB---_1RF0RA_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM74.

Module TM84.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LB_1LE0RD_0LC---_1RF0RA_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM84.

Module TM85.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE0RF_1RA0RB_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM85.

Module TM194.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1LD0RA_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D B [1;1;0] [1;0;1] 5 10 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM194.

Module TM195.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1RC1RE_1LD1RF_1LA0LD_1LA0RB_1RB---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A C [1;1;0] [1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM195.

Module TM196.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC1LB_1RD1RA_1LE1RF_1LB0LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B D [1;1;0] [1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM196.

Module TM197.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC1LB_1RD1RA_1LE1RF_0LC0LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B D [1;1;0] [1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM197.

Module TM198.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC1RE_1LD---_1RB1LD_1RF0RB_1LA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D F [1;1;1;0] [1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM198.

Module TM199.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1LB_1LA1RD_1RE0RC_1LF0RA_1LC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B E [1;1;1;0] [1;1;0;1] 3 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM199.

Module TM200.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC0LB_1LD1RF_1LE---_1RC1LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;0] [1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM200.

Module TM201.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0RE_1LD0LC_1LE1RA_1LF---_1RD1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F B [1;1;1;0] [1;1;0;1] 4 8 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM201.

Module TM202.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0RC0LB_1LE1RD_1RA0RC_1LF---_1RC1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;0] [1;1;0;1] 5 10 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM202.

Module TM203.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC0RE_0RD0LC_1LE1RA_1LF---_1RD1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F B [1;1;1;0] [1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM203.

Module TM204.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC---_1RA1LC_1RE0RA_1LF0RB_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C E [1;1;1;0] [1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM204.

Module TM205.
Definition tm := Eval compute in (TM_from_str "1LB0RE_0RC0LB_1LE1RD_1RA0RC_1LF---_1RC0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;0] [1;1;0;1] 5 10 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM205.

Module TM206.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC---_1RA0RE_1RF0RA_0RA0LE_1LE0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C F [1;1;1;0] [1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM206.

Module TM207.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RF_1LA1RD_1RE0RC_1LF0RA_0RC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B E [1;1;1;0] [1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM207.

Module TM208.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC---_1RD1LC_1LB1RE_1RF0RD_1LA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C F [1;1;1;0] [1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM208.

Module TM209.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RD_1RD0LC_1LE---_1RF1LE_1LD1RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E B [1;1;1;0] [1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM209.

Module TM210.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RD_1RD0LC_1LE---_1RF1LE_0LC1RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E B [1;1;1;0] [1;1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM210.

Module TM211.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0LC1RE_1RD0LC_1LA---_1RF0RB_1LC0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A F [1;1;1;0] [1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM211.

Module TM213.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0RD_1RE1RA_---1LA_1LF1RB_0LC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B E [1;1;0] [1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM213.

Module TM215.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0RD_1RE1RA_---1LA_1LF1RB_1LB0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B E [1;1;0] [1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM215.

Module TM216.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RE_1LD1RA_1LA0LD_1LA0RB_---1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A C [1;1;0] [1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM216.

Module TM217.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LD0RA_---1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D B [1;1;0] [1;0;1] 5 10 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM217.

Module TM218.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC0RD_1RF1RA_---1LE_1LB0LE_1LE1RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B F [1;1;0] [1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM218.

Module TM219.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RD_1LD0LC_1RA0RF_1LD0RA_---1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D B [1;1;0] [1;0;1] 5 10 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM219.

Module TM220.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1LC0LB_1RD0RF_1RA1RE_1LC0RD_---1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C A [1;1;0] [1;0;1] 2 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM220.


Module V1a.
Section V1a.
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
  ldh <* ld0^^(n+1) |> [0;0] *> r.

Hypothesis LOv_1:
  forall r n,
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(n+1) <* ld1 |> r.

Hypothesis ROv2_0_0:
  forall l r n,
  l |> rd1^^(n*2) *> rm2 *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0;0] *> r.

Hypothesis ROv2_0_1:
  forall l r n,
  l |> rd1^^(n*2) *> rm2 *> rd1 *> r -->+
  l <* ld1 <* ld0^^(n*3+2) <* ld1 |> r.

Hypothesis ROv2_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> rm2 *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.

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

Lemma RC2_Ov_0_0 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 ((m*2+1)*2^i*2) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_0_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (0*2) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1) |> RC 0.
Proof.
  epose proof (ROv2_0_0 _ 0inf _) as I1.
  solve_rule I1.
Qed.

Lemma RC2_Ov_0_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (m*2+1) -->+
  LC (lenL+1+lenR*3+1+1+1) (((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2) |> RC m.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 m -->+
  LC (lenL+1+lenR*3+1+1+1) (((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1) |> RC m.
Proof.
  solve_rule ROv2_1.
Qed.

Lemma LC_Ov_0 lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i*2) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC2 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv_0.
Qed.

Lemma LC_Ov_1 lenL n:
  LC lenL O <| RC (n*2+1) -->+
  LC (lenL+1+1) (((2^lenL-1)*2+1)*2) |> RC n.
Proof.
  solve_rule LOv_1.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL*2 /\ k<2^lenL
| cfgR lenL k n => 1 <= k+n+1 < 2^lenL*2 /\ k<2^lenL
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
    + divmod2_cases n.
      * lowbit_cases n'.
        1: lia.
        eexists (cfgR2 _ _ _ _ _). split.
        1: apply LC_Ov_0.
        spl.
        pose proof (split_bound_v1 x i lenL).
        lia.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_1.
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
      * lowbit_cases n'0.
        -- eexists (cfgR _ _ _). split.
           1: apply RC2_Ov_0_0_0; lia.
           spl.
           rw_pa.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
           lia.
        -- eexists (cfgR2 _ _ _ _ _). split.
           1: apply RC2_Ov_0_0; lia.
           spl.
           zify_le_mul_r; lia.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_1; lia.
        spl.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        remember (n'*3).
        zify_pow2sub1; lia.
    + eexists (cfgR _ _ _). split.
      1: apply RC2_Ov_1; lia.
      spl.
      rw_pa.
      pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
      remember (n'*3).
      zify_pow2sub1; lia.
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

End V1a.
End V1a.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC---_1RD1LC_1LF1RE_0LA0RD_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 2 2 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC0LB_1LD1RD_1RE---_1RA1LE_0LC0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM8.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC0LB_1LD1RD_1RE---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM9.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1LB1RB_1RC---_1RD1LC_1LF1RE_1RC0RD_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 2 2 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM10.

Module TM64.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE1RF_1RA0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 2 2 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM64.

Module TM65.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC0LB_1LF1RD_1RE---_1RA1LE_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ E A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM65.

Module TM75.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LB_1LE1RD_0LA---_1RF0RA_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ F A [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM75.

Module TM76.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC0RD_1RD1LC_1LE1RB_0RA0LE_0LD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ C D [1;1;1;0;0] [1;1;1;0;1] 2 2 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM76.

Module TM77.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RE_0LB---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 5 19 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM77.

Module TM78.
Definition tm := Eval compute in (TM_from_str "1LB1RB_0LC---_1LD1RE_0RA0LD_1RF0RC_1RC1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ F C [1;1;1;0;0] [1;1;1;0;1] 2 2 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM78.

Module TM79.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0RC0LB_1LD1RD_0LA---_1RF0RA_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ F A [1;1;1;0;0] [1;1;1;0;1] 4 3 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM79.

Module TM80.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LB_1LD1RA_0RE0LD_1LF1RF_0LC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ B C [1;1;1;0;0] [1;1;1;0;1] 1 0 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM80.

Module V1b.
Section V1b.
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

Hypothesis LOv_O:
  forall r n,
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1^^2 |> r.

Hypothesis LOv_S:
  forall r n m,
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv2_0_0:
  forall l r n,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) <* ld1^^2 |> r.

Hypothesis ROv2_0_1:
  forall l r n m,
  l |> rd1^^(n*2) *> [1;0;1;0;0] *> rd1^^(1+m) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*3+1) <* ld1 |> [0;0] *> rd0^^m *> rd1 *> r.

Hypothesis ROv2_1:
  forall l r n,
  l |> rd1^^(n*2+1) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+3) |> r.

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

Lemma RC2_Ov_0_0 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (m*2) -->+
  LC (lenL+1+lenR*3+1+1+1) (((((k*2+1)*2^(lenR*3)-1)*2+1)*2)*2) |> RC m.
Proof.
  solve_rule ROv2_0_0.
Qed.

Lemma RC2_Ov_0_1 lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2) 0 (((m*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1+lenR*3+1+1) ((((k*2+1)*2^(lenR*3)-1)*2+1)*2) |> RC2 i ((2^i-1)*2+1) m.
Proof.
  solve_rule ROv2_0_1.
Qed.

Lemma RC2_Ov_1 lenL lenR k m:
  k<2^lenL ->
  LC lenL k |> RC2 (lenR*2+1) 0 m -->+
  LC (lenL+1+lenR*3+1+1+1) (((((k*2+1)*2^(lenR*3)-1)*2+1)*2+1)*2+1) |> RC m.
Proof.
  solve_rule ROv2_1.
Qed.

Lemma LC_Ov_0 lenL n:
  LC lenL O <| RC (n*2) -->+
  LC (lenL+1+1) (((2^lenL-1)*2)*2) |> RC n.
Proof.
  solve_rule LOv_O.
Qed.

Lemma LC_Ov_1 lenL n i:
  LC lenL O <| RC (((n*2+1)*2^i-1)*2+1) -->+
  LC (lenL+1) ((2^lenL-1)*2) |> RC2 i ((2^i-1)*2+1) n.
Proof.
  solve_rule LOv_S.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n+1 < 2^lenL*2 /\ k<2^lenL
| cfgR lenL k n => 1 <= k+n+2 < 2^lenL*2 /\ k<2^lenL
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
    + divmod2_cases n.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        spl.
      * lowbitS_cases n'.
        eexists (cfgR2 _ _ _ _ _). split.
        1: apply LC_Ov_1.
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
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    divmod2_cases lenR.
    + divmod2_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0_0; lia.
        spl.
        rw_pa.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
        remember (n'*3).
        zify_pow2sub1; lia.
      * lowbitS_cases n'0.
        eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_0_1; lia.
        spl.
        zify_le_mul_r; lia.
    + eexists (cfgR _ _ _). split.
      1: apply RC2_Ov_1; lia.
      spl.
      rw_pa.
      pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(n'*3))).
      remember (n'*3).
      zify_pow2sub1; lia.
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

End V1b.
End V1b.

Module TM66.
Definition tm := Eval compute in (TM_from_str "1RB---_1LC1RE_0RD0LC_1LE1RA_1RF0RB_1RB1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1b.nonhalt _ F B [1;1;1;0;0] [1;1;1;0;1] 4 13 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM66.

Module TM86.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RD0LC_1LE0RF_1RA0RB_0LE---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1b.nonhalt _ A B [1;1;1;0;0] [1;1;1;0;1] 4 13 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM86.


