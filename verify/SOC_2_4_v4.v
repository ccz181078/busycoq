From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat.
Require Import Lia PeanoNat String List.
Import BinDigits.

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
  follow10 H;
  simpl_rotate;
  simpl_tape;
  finish.

Ltac solve_rule H :=
  intros;
  unfold LC,RC,RC1,RC2;
  rw_Bin; try solve[solve_pow2_lt]; follow' H.


Module V5.
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

Hypothesis LOv:
  forall r n m,
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld0<+ld1)^^m <* ld1 |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld0<+ld1)^^m <* ld1 |> [1;0;0] *> r.

Definition LOv_ls m :=
  <[D0;D1]^^m <+ [D1].

Definition ROv2_ls n m :=
  [D1] <+ [D0]^^(n*2+2) <+ <[D0;D1]^^m <+ [D1].

Lemma val1_LOv_ls_lb m:
  val1 (LOv_ls m) >= 1.
Proof.
  unfold LOv_ls.
  cbn. lia.
Qed.

Lemma val1_ROv2_ls_lb n m:
  val1 (ROv2_ls n m) >=1.
Proof.
  unfold ROv2_ls.
  cbn. lia.
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

Lemma RC2_Ov lenL lenR k i i0 m:
  let ls := ROv2_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC2 i0 ((2^i0-1)*2) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv2_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  let ls := ROv2_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv2_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i i0:
  let ls := LOv_ls i in
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC2 i0 ((2^i0-1)*2) n.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  let ls := LOv_ls i in
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL2(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL2 lenL k lenR n m => LC lenL k <| RC2 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgR lenL k n => k+n < 2^lenL
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
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        pose proof (val_spec (LOv_ls i)).
        pose proof (val1_LOv_ls_lb i).
        solve_pow2_lt.
        rewrite <-Nat.add_assoc.
        apply muladd_mul_lt; lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply LC_Ov.
        pose proof (val_spec (LOv_ls i)).
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v1 x0 i0 lenL).
        zify_le_mul_r.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        pose proof (val_spec (ROv2_ls lenR i)).
        pose proof (val1_ROv2_ls_lb lenR i).
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^length (ROv2_ls lenR i))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        3: solve_pow2_lt.
        2:{
          pose proof (val_spec (ROv2_ls lenR i)).
          solve_pow2_lt.
          apply muladd_mul_lt; lia.
        }
        pose proof (split_bound_v2 x0 i0).
        zify_le_mul_r.
        lia.
    + eexists (cfgL2 _ _ _ _ _). split.
      1: apply RC2_Inc; lia.
      lia.
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


Module TM196.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_1LC1LA_---0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM196.

Module TM197.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LB1LD_1RA1RF_1RD0RB_---0LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 3 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM197.

Module TM199.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0RA1LD_1RD0RA_1RE1RF_1RA1LE_---0LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ E A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM199.

Module TM200.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0RB1LD_1RA1RF_1RD0RB_---0LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 3 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM200.

Module TM201.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_0RC1LA_---0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM201.

Module TM214.
Definition tm := Eval compute in (TM_from_str "1LB1LD_1RC1LB_1LF1RD_1RE0RC_1RB---_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 5 7 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM214.

Module TM215.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1LE_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 3 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM215.

Module TM216.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LB1LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM216.

Module TM217.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1RC0LB_1LF1LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ F A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM217.

Module TM223.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RF_1RA---_1RE0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 3 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM223.

Module TM224.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA1RF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM224.

Module TM225.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0RC0LB_1LE1RD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5.nonhalt _ F A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM225.

Module V5a.
Section V5a.
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
  forall r n m,
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld1<+ld0)^^m <* ld1^^2 |> [1] *> r.

Hypothesis ROv1:
  forall l r n m,
  l |> rd1^^n *> rm1 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld0<+ld1)^^m <* ld1 |> [1] *> r.

Definition LOv_ls m :=
  <[D1;D0]^^m <+ [D1]^^2.

Definition ROv1_ls n m :=
  [D1] <+ [D0]^^(n*2+2) <+ <[D0;D1]^^m <+ [D1].

Lemma val1_LOv_ls_lb m:
  val1 (LOv_ls m) >= 1.
Proof.
  unfold LOv_ls.
  cbn. lia.
Qed.

Lemma val1_ROv1_ls_lb n m:
  val1 (ROv1_ls n m) >=1.
Proof.
  unfold ROv1_ls.
  cbn. lia.
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

Lemma RC1_Ov lenL lenR k i i0 m:
  let ls := ROv1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k i:
  let ls := ROv1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1.
Qed.

Lemma LC_Ov lenL n i i0:
  let ls := LOv_ls i in
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2) n.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  let ls := LOv_ls i in
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgR lenL k n => k+n < 2^lenL
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        pose proof (val_spec (LOv_ls i)).
        pose proof (val1_LOv_ls_lb i).
        solve_pow2_lt.
        rewrite <-Nat.add_assoc.
        apply muladd_mul_lt; lia.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        pose proof (val_spec (LOv_ls i)).
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v1 x0 i0 lenL).
        zify_le_mul_r.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR1 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (val_spec (ROv1_ls lenR i)).
        pose proof (val1_ROv1_ls_lb lenR i).
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^length (ROv1_ls lenR i))).
        solve_pow2_lt.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        3: solve_pow2_lt.
        2:{
          pose proof (val_spec (ROv1_ls lenR i)).
          solve_pow2_lt.
          apply muladd_mul_lt; lia.
        }
        pose proof (split_bound_v2 x0 i0).
        zify_le_mul_r.
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
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

End V5a.
End V5a.

Module TM202.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD1RB_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ D A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM202.

Module TM203.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RF0LE_1LC1RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 4 13 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM203.

Module TM204.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA1RC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 4 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM204.

Module TM205.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LB_1LF1RD_1RE0RC_1RB---_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 5 21 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM205.

Module TM206.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LB1RD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 3 3 3).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM206.

Module TM210.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1RD0LC_1LA0RA_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 4 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM210.

Module TM211.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RC_1RD1LC_1LA1RE_1RF0RD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 3 5 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM211.

Module TM212.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LD0RD_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ D A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM212.

Module TM213.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1RF0LE_1LC0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5a.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 5 7 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM213.

Module V5b.
Section V5b.
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
  forall r n m,
  ldh <* ld1^^n <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld0<+ld1)^^m <* ld1 <* ld0 |> [1] *> r.

Hypothesis ROv1:
  forall l r n m,
  l |> rd1^^n *> rm1 *> rd1^^m *> rd0 *> r -->+
  l <* ld0 <* ld1^^(n*2+3) <* (ld0<+ld1)^^m |> [0] *> r.

Definition LOv_ls m :=
  <[D0;D1]^^m <+ <[D1;D0].

Definition ROv1_ls n m :=
  [D0] <+ [D1]^^(n*2+3) <+ <[D0;D1]^^m.

Lemma val1_LOv_ls_lb m:
  val1 (LOv_ls m) >= 2.
Proof.
  unfold LOv_ls.
  cbn. lia.
Qed.

Lemma val1_ROv1_ls_lb n m:
  val1 (ROv1_ls n m) >=7.
Proof.
  unfold ROv1_ls.
  cbn.
  apply val1_app_ge.
  rewrite Nat.add_comm; cbn.
  lia.
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

Lemma RC1_Ov lenL lenR k i i0 m:
  let ls := ROv1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k i:
  let ls := ROv1_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv1_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv1.
Qed.

Lemma LC_Ov lenL n i i0:
  let ls := LOv_ls i in
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC1 i0 ((2^i0-1)*2) n.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  let ls := LOv_ls i in
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL1(lenL k lenR n m:nat)
| cfgR1(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL1 lenL k lenR n m => LC lenL k <| RC1 lenR n m
| cfgR1 lenL k lenR n m => LC lenL k |> RC1 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgR lenL k n => k+n < 2^lenL
| cfgL1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
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
    + lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        pose proof (val_spec (LOv_ls i)).
        pose proof (val1_LOv_ls_lb i).
        solve_pow2_lt.
        rewrite <-Nat.add_assoc.
        apply muladd_mul_lt; lia.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        pose proof (val_spec (LOv_ls i)).
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v1 x0 i0 lenL).
        zify_le_mul_r.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR1 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        pose proof (val_spec (ROv1_ls lenR i)).
        pose proof (val1_ROv1_ls_lb lenR i).
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^length (ROv1_ls lenR i))).
        solve_pow2_lt.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        3: solve_pow2_lt.
        2:{
          pose proof (val_spec (ROv1_ls lenR i)).
          solve_pow2_lt.
          apply muladd_mul_lt; lia.
        }
        pose proof (split_bound_v2 x0 i0).
        zify_le_mul_r.
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
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

End V5b.
End V5b.

Module TM218.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC---_1RD1LC_1LF1RE_1RB0RD_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5b.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 0).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM218.

Module TM219.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0RE0LD_1LA1RD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5b.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 2 3 0).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM219.

Module TM220.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0RD0LC_1LE1RC_1RA---_1RE0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5b.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 4 11 0).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM220.

Module TM221.
Definition tm := Eval compute in (TM_from_str "1LB0RC_1RC---_1RD1LC_1LF1RE_1RB0RD_0RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5b.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 0).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM221.

Module TM222.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0RC0LB_1LE0RD_1RA1LD_1RD---_1RE0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5b.nonhalt _ D A [1;1;1;0;0;0] [1;1;1;1;0;1] 4 11 0).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM222.

Module V5c.
Section V5c.
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
  forall r n m,
  ldh <* ld1^^(1+n) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* (ld1<+ld0)^^m <* ld1 |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+1) <* ld1 <* (ld1<+ld0)^^m <* ld1 |> [1;0;0] *> r.

Definition LOv_ls m :=
  <[D1;D0]^^m <+ [D1].

Definition ROv2_ls n m :=
  [D1] <+ [D0]^^(n*2+1) <+ [D1] <+ <[D1;D0]^^m <+ [D1].

Lemma val1_LOv_ls_lb m:
  val1 (LOv_ls m) >= 1.
Proof.
  unfold LOv_ls.
  cbn. lia.
Qed.

Lemma val1_ROv2_ls_lb n m:
  val1 (ROv2_ls n m) >=1.
Proof.
  unfold ROv2_ls.
  cbn. lia.
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

Lemma RC2_Ov lenL lenR k i i0 m:
  let ls := ROv2_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC2 i0 ((2^i0-1)*2) m.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv2_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  let ls := ROv2_ls lenR i in
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls Hk.
  unfold ls,LC,RC,RC1,RC2,ROv2_ls.
  rewrite BinDec_app by lia.
  simpl_flat_map.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i i0:
  let ls := LOv_ls i in
  LC (1+lenL) O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+1+length ls) ((2^lenL-1)*2*2^length ls+val0 ls) |> RC2 i0 ((2^i0-1)*2) n.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by solve_pow2_lt.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  let ls := LOv_ls i in
  LC (1+lenL) O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+1+length ls) ((2^lenL-1)*2*2^length ls+val0 ls) |> RC 1.
Proof.
  intros ls.
  unfold ls,LC,RC,RC1,RC2,LOv_ls.
  rewrite BinDec_app by solve_pow2_lt.
  simpl_flat_map.
  solve_rule LOv.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgL2(lenL k lenR n m:nat)
| cfgR2(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgL2 lenL k lenR n m => LC lenL k <| RC2 lenR n m
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => lenL<>O /\ 1 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgR lenL k n => lenL<>O /\ k+n < 2^lenL
| cfgL2 lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR2 lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct lenL. 1: lia.
      lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        repeat split; try lia.
        pose proof (val_spec (LOv_ls i)).
        pose proof (val1_LOv_ls_lb i).
        solve_pow2_lt.
        rewrite <-Nat.add_assoc.
        apply muladd_mul_lt; lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply LC_Ov.
        pose proof (val_spec (LOv_ls i)).
        pose proof (split_bound_v1 x0 i0 (S lenL)).
        cbn[Nat.pow] in *.
        repeat split; try lia.
        3: solve_pow2_lt.
        -- zify_le_mul_r; lia.
        -- solve_pow2_lt.
           apply muladd_mul_lt; lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        pose proof (val_spec (ROv2_ls lenR i)).
        pose proof (val1_ROv2_ls_lb lenR i).
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^length (ROv2_ls lenR i))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        3: solve_pow2_lt.
        2:{
          pose proof (val_spec (ROv2_ls lenR i)).
          solve_pow2_lt.
          apply muladd_mul_lt; lia.
        }
        pose proof (split_bound_v2 x0 i0).
        zify_le_mul_r.
        lia.
    + eexists (cfgL2 _ _ _ _ _). split.
      1: apply RC2_Inc; lia.
      lia.
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

End V5c.
End V5c.

Module TM198.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LB_1LD1RF_0LF1LA_---0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5c.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM198.

Module TM207.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC1LB_1LF1RD_1RE0RC_1RB---_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5c.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 6 11 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM207.

Module TM208.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1LB_1RD1LC_1LA1RE_1RF0RD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5c.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM208.

Module TM209.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1RE0LD_1LB1LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V5c.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM209.


Module V6.
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
  forall r n m,
  ldh <* ld1^^n <| rd1^^(m*2) *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld1<+ld1<+ld0<+ld0)^^m <* ld1 |> [0;0;0] *> r.

Hypothesis LOv_1:
  forall r n m,
  ldh <* ld1^^n <| rd1^^(m*2+1) *> rd0 *> r -->+
  ldh <* ld0^^n <* (ld1<+ld1<+ld0<+ld0)^^(m+1) |> [0] *> r.

Hypothesis ROv1_0:
  forall l r n m,
  l |> rd1^^n *> rm1 *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld1<+ld0<+ld0<+ld1)^^m |> [0;0;0] *> r.

Hypothesis ROv1_1:
  forall l r n m,
  l |> rd1^^n *> rm1 *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld1<+ld0<+ld0<+ld1)^^m <* ld1 <* ld0 <* ld0 |> [0] *> r.

Hypothesis ROv2_0:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^(m*2) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld0<+ld0<+ld1<+ld1)^^m <* ld0^^2 |> [0] *> r.

Hypothesis ROv2_1:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^(m*2+1) *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2+2) <* (ld0<+ld0<+ld1<+ld1)^^m <* ld0^^2 <* ld1 |> [0;0;0] *> r.

Inductive Rtp := R1 | R2.

Definition LOv_ls m :=
  match m mod 2 with
  | O => <[D1;D1;D0;D0]^^(m/2) <+ [D1]
  | S O => <[D1;D1;D0;D0]^^(m/2+1)
  | _ => []
  end.

Definition LOv_tp m :=
  match m mod 2 with
  | O => R2
  | S O => R1
  | _ => R1
  end.

Definition ROv_ls n m tp :=
  match tp with
  | R1 =>
    match m mod 2 with
    | O => [D1] <+ [D0]^^(n*2+2) <+ <[D1;D0;D0;D1]^^(m/2)
    | S O => [D1] <+ [D0]^^(n*2+2) <+ <[D1;D0;D0;D1]^^(m/2) <+ <[D1;D0;D0]
    | _ => []
    end
  | R2 =>
    match m mod 2 with
    | O => [D1] <+ [D0]^^(n*2+2) <+ <[D0;D0;D1;D1]^^(m/2) <+ <[D0;D0]
    | S O => [D1] <+ [D0]^^(n*2+2) <+ <[D0;D0;D1;D1]^^(m/2) <+ <[D0;D0;D1]
    | _ => []
    end
  end.

Definition ROv_tp m tp :=
  match tp with
  | R1 =>
    match m mod 2 with
    | O => R2
    | S O => R1
    | _ => R1
    end
  | R2 =>
    match m mod 2 with
    | O => R1
    | S O => R2
    | _ => R2
    end
  end.

Lemma val1_LOv_ls_lb m:
  val1 (LOv_ls m) >= 1.
Proof.
  unfold LOv_ls.
  destruct (m mod 2) as [|[|]] eqn:Em. 3: lia.
  - cbn. lia.
  - rewrite Nat.add_comm.
    cbn. lia.
Qed.

Lemma val1_ROv_ls_lb tp n m:
  val1 (ROv_ls n m tp) >=1.
Proof.
  unfold ROv_ls.
  destruct (m mod 2) as [|[|]] eqn:Em. 3: lia.
  all: destruct tp.
  all: repeat ((cbn; lia) || apply val1_app_ge).
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

Definition RCx tp len n m :=
  match tp with
  | R1 => RC1 len n m
  | R2 => RC2 len n m
  end.

Lemma RCx_Inc tp len n m l:
  1+n<2^(len+1) ->
  l |> RCx tp len (1+n) m -->+
  l <| RCx tp len n m.
Proof.
  intros H.
  destruct tp;
  apply RBinDec2_spec; try lia;
  follow' RInc.
Qed.

Lemma RCx_Ov tp lenL lenR k i i0 m:
  let ls := ROv_ls lenR i tp in
  k<2^lenL ->
  LC lenL k |> RCx tp lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RCx (ROv_tp i tp) i0 ((2^i0-1)*2+1) m.
Proof.
  intros ls Hk.
  unfold ls,RCx,LC,RC,RC1,RC2,ROv_ls,ROv_tp.
  remember (i/2) as v1.
  remember (i mod 2) as v2.
  destruct v2 as [|[|]]. 3: lia.
  1,2: destruct tp.
  all:
  rewrite BinDec_app by lia;
  simpl_flat_map.
  - replace i with (v1*2) by lia.
    solve_rule ROv1_0.
  - replace i with (v1*2) by lia.
    solve_rule ROv2_0.
  - replace i with (v1*2+1) by lia.
    solve_rule ROv1_1.
  - replace i with (v1*2+1) by lia.
    solve_rule ROv2_1.
Qed.

Lemma RCx_Ov_0 tp lenL lenR k i:
  let ls := ROv_ls lenR i tp in
  k<2^lenL ->
  LC lenL k |> RCx tp lenR 0 ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) (k*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls Hk.
  unfold ls,RCx,LC,RC,RC1,RC2,ROv_ls,ROv_tp.
  remember (i/2) as v1.
  remember (i mod 2) as v2.
  destruct v2 as [|[|]]. 3: lia.
  1,2: destruct tp.
  all:
  rewrite BinDec_app by lia;
  simpl_flat_map.
  - replace i with (v1*2) by lia.
    solve_rule ROv1_0.
  - replace i with (v1*2) by lia.
    solve_rule ROv2_0.
  - replace i with (v1*2+1) by lia.
    solve_rule ROv1_1.
  - replace i with (v1*2+1) by lia.
    solve_rule ROv2_1.
Qed.

Lemma LC_Ov lenL n i i0:
  let ls := LOv_ls i in
  LC lenL O <| RC ((((n*2+1)*2^i0)*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RCx (LOv_tp i) i0 ((2^i0-1)*2+1) n.
Proof.
  intros ls.
  unfold ls,RCx,LC,RC,RC1,RC2,LOv_ls,LOv_tp.
  remember (i/2) as v1.
  remember (i mod 2) as v2.
  destruct v2 as [|[|]]. 3: lia.
  all:
  rewrite BinDec_app by lia;
  simpl_flat_map.
  - replace i with (v1*2) by lia.
    solve_rule LOv_0.
  - replace i with (v1*2+1) by lia.
    solve_rule LOv_1.
Qed.

Lemma LC_Ov_0 lenL i:
  let ls := LOv_ls i in
  LC lenL O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+length ls) ((2^lenL-1)*2^length ls+val0 ls) |> RC 0.
Proof.
  intros ls.
  unfold ls,RCx,LC,RC,RC1,RC2,LOv_ls,LOv_tp.
  remember (i/2) as v1.
  remember (i mod 2) as v2.
  destruct v2 as [|[|]]. 3: lia.
  all:
  rewrite BinDec_app by lia;
  simpl_flat_map.
  - replace i with (v1*2) by lia.
    solve_rule LOv_0.
  - replace i with (v1*2+1) by lia.
    solve_rule LOv_1.
Qed.

Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgLx(tp:Rtp)(lenL k lenR n m:nat)
| cfgRx(tp:Rtp)(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgLx tp lenL k lenR n m => LC lenL k <| RCx tp lenR n m
| cfgRx tp lenL k lenR n m => LC lenL k |> RCx tp lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 1 <= k+n < 2^lenL+1 /\ k<2^lenL
| cfgR lenL k n => k+n < 2^lenL
| cfgLx tp lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgRx tp lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1)
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
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply LC_Ov_0.
        pose proof (val_spec (LOv_ls i)).
        pose proof (val1_LOv_ls_lb i).
        solve_pow2_lt.
        rewrite <-Nat.add_assoc.
        apply muladd_mul_lt; lia.
      * eexists (cfgRx _ _ _ _ _ _). split.
        1: apply LC_Ov.
        pose proof (val_spec (LOv_ls i)).
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v1 x0 i0 lenL).
        zify_le_mul_r.
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgRx _ _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: apply RCx_Ov_0; lia.
        pose proof (val_spec (ROv_ls lenR i tp)).
        pose proof (val1_ROv_ls_lb tp lenR i).
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^length (ROv_ls lenR i tp))).
        solve_pow2_lt.
      * eexists (cfgRx _ _ _ _ _ _). split.
        1: apply RCx_Ov; lia.
        repeat split; try lia.
        3: solve_pow2_lt.
        2:{
          pose proof (val_spec (ROv_ls lenR i tp)).
          solve_pow2_lt.
          apply muladd_mul_lt; lia.
        }
        pose proof (split_bound_v2 x0 i0).
        zify_le_mul_r.
        lia.
    + eexists (cfgLx _ _ _ _ _ _). split.
      1: apply RCx_Inc; lia.
      lia.
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

Module TM226.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RD_1LD1RF_1RE0LD_1LE1LB_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM226.

Module TM227.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1RC0LB_1LC1LD_1RA0RB_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ D A [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 0).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM227.

Module TM228.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RE_1LE1RA_1RF0LE_1LF1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 0).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM228.

Module TM229.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RE_1RD0LC_1LD1LA_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 4 3 1).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM229.

Module TM230.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RE_1RF0RA_0RA0LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ C A [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 0).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM230.

Module TM231.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LA0LD_0RB0LD_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ A B [1;1;1;0;0;0] [1;1;1;1;0;1] 4 3 1).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM231.

Module TM232.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RE_1LD1RF_1LB0LE_0RC0LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 1 1 1).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM232.

Module TM233.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RF_1LE1RA_1LC0LF_0RD0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V6.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 0).
  1-8: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM233.

