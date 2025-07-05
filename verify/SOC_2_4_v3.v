From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

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

Ltac rw_unrotate_0 :=
  (rewrite lpow_unrotate_1 ||
  rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 ||
  rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 ||
  rewrite lpow_unrotate_6).

Ltac rw_unrotate :=
  cbn;
  repeat rw_unrotate_0.

Ltac es1 :=
  (apply evstep_refl ||
  use_shift_rule ||
  (step1) ||
  (simpl_rotate; step1)).

Ltac urstep :=
  rw_unrotate; es1.

Lemma DH_R_def (q:Q) (l r:side) (m:Sym):
  l {{q}}> (m>>r) = (q,(l,m,r)).
Proof.
  reflexivity.
Qed.

Ltac fold_DH_R :=
  (
  match goal with
  | |- context[(?q,(?l,?m,?r))] =>
    lazymatch m with
    | hd _ => fail
    | _ => rewrite <-(DH_R_def q l r m)
    end
  end).

Ltac rw_unrotate_r :=
  cbn;
  repeat (
  fold_DH_R ||
  rw_unrotate_0).

Ltac urstep_r :=
  rw_unrotate_r;
  es1.

Ltac es := intros; st; repeat urstep.
Ltac es_r := intros; st; repeat urstep_r.

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
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.

Hypothesis LOv:
  forall r n,
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^n |> [1] *> r.

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2_O:
  forall l r,
  l |> rd1^^0 *> rm3 *> r -->+
  l <* ld1 <* ld0 |> [1;0;0] *> r.

Hypothesis ROv2_S:
  forall l r n,
  l |> rd1^^(1+n) *> rm3 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) <* ld0 <* ld1 |> [1;0;0] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov_S lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (1+lenR) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2+1+1) (((((k*2+1)*2+1)*2^(lenR*2)-1)*2+1)*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC2_Ov_S_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR*2+1+1) (((((k*2+1)*2+1)*2^(lenR*2)-1)*2+1)*2) |> RC 1.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC2_Ov_O lenL k i m:
  k<2^lenL ->
  LC lenL k |> RC2 0 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC2_Ov_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |> RC2 0 0 0 -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC 1.
Proof.
  solve_rule ROv2_O.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m;
      destruct lenR as [|lenR].
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_O_0; lia.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_S_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V1.
End V1.

Module TM67.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0RF_1RD0RB_---1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM67.

Module TM68.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC0RF_1RD1LC_1LE1RA_1LB0LE_---1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM68.

Module TM69.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0RF_1RA1LD_1RC0RA_---1LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM69.

Module TM70.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD1RF_1RA1LD_1RC0RA_---0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM70.

Module TM71.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC1RF_1RD1LC_1LE1RA_1LB0LE_---0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM71.

Module TM72.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1RF_1RD0RB_---0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM72.

Module TM73.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1LD1RE_---1RF_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM73.

Module TM74.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_0RB0LC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM74.

Module TM75.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_0RD0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM75.

Module TM76.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0LF0LD_1RE0LC_1RA---_1RE0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM76.

Module TM77.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1RF0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM77.

Module TM78.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_0RF0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 4 11 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM78.

Module TM79.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1LA0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM79.

Module TM80.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RF_0LF0LD_1LE0LC_1RA---_1RE0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM80.

Module TM81.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_1LB0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM81.

Module TM82.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1LB0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 7 75 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM82.

Module TM83.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_1LB0LC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM83.

Module TM84.
Definition tm := Eval compute in (TM_from_str "1LB0LC_1LC1RD_0LD0LA_1RE0RB_1RF---_1RB1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM84.

Module TM85.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_1RC0LC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM85.

Module TM86.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_1RE0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM86.

Module TM87.
Definition tm := Eval compute in (TM_from_str "1RB0LB_0LC0LA_1RE0RD_1LB1RC_1RF---_1RD1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F D [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM87.

Module TM88.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_1LD0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 10 559 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM88.

Module TM89.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_1LE0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 6 43 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM89.

Module TM90.
Definition tm := Eval compute in (TM_from_str "1LB0LB_0LC0LA_1RD0RF_1RE---_1RF1LE_1LB1RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E F [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM90.

Module TM91.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LF_1RD0RA_1RE---_1RA1LE_---0LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM91.

Module TM92.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_0RC0LC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM92.

Module TM93.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_0LE0LD_0LB0LC_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM93.

Module TM94.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_0LF0LE_0LC0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 4 5 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM94.

Module TM95.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_0LA0LF_0LD0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 3 3 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM95.

Module TM96.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC0LB_1RE0RD_1LB1RC_1RF---_1RD1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F D [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM96.

Module TM97.
Definition tm := Eval compute in (TM_from_str "1LB---_1LC1RD_0LD0LC_1RE0RB_1RF---_1RB1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM97.

Module TM98.
Definition tm := Eval compute in (TM_from_str "1LB---_0LC0LB_1RD0RF_1RE---_1RF1LE_1LB1RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E F [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM98.

Module TM99.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC0RD_1RE1RA_1LF1RB_1RD1LE_0LB0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E D [1;1;1;1] [0;1;0;1] 3 3 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM99.

Module TM100.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LD1RE_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM100.

Module TM103.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA0LE_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM103.

Module TM104.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RC0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM104.

Module TM105.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD0LE_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM105.

Module TM106.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LF0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM106.

Module TM107.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0LD0LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM107.

Module TM108.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_0RD0LE_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM108.

Module TM109.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_0RA0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM109.

Module TM110.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM110.

Module TM111.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_0LA0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM111.

Module TM112.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0RA0LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM112.

Module TM113.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC---_1RD1LC_1LF1RE_1RB0RD_1LA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM113.

Module TM114.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1LA0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 7 75 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM114.

Module TM115.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RD0LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM115.

Module TM116.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LD1RF_1LE0LD_1RF0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ B C [1;1;1;1] [0;1;0;1] 4 11 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM116.

Module TM117.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC0LC_1RE0RD_1LA1RC_1RF---_1RD1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F D [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM117.

Module TM118.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RA0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 2 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM118.

Module TM119.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0RC0LD_1RE0RA_1RF---_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM119.

Module TM120.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1LC1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM120.

Module TM121.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1LD1LC_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM121.

Module TM122.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA1LD_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM122.

Module TM123.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1LA0LE_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM123.

Module TM124.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1LD0LE_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM124.

Module TM125.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1LC0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM125.

Module TM126.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1LF_0RF1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ E A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM126.

Module TM143.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1RD1LC_1RA1LD_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ D A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM143.

Module TM144.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC1RE_1LD0LC_1RA1LD_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM144.

Module TM145.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LC_1LE1RA_1LF0LE_1RC1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ C D [1;1;1;1] [0;1;0;1] 2 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM145.

Module TM146.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_0LE---_1RF1RE_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM146.

Module TM147.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_0RD0RA_1LE---_1RE1RF_1RA1LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1.nonhalt _ F A [1;1;1;1] [0;1;0;1] 3 3 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM147.


Module V2.
Section V2.
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
  ldh <* ld0^^(1+n) |> [1] *> r.

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> [1;0;0] *> r.

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
  solve_rule ROv1.
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
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2) n.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2,3: solve_pow2_lt.
      pose proof (split_bound_v1 x i (lenL+1)).
      rewrite Nat.pow_add_r in *.
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2.
End V2.

Module TM11.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1RC---_1RD1LA_1LF1RE_1RB0RD_1LA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ C D [1;1] [0;1] 8 47 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM11.

Module TM12.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LE_1LD1RF_1LE0LD_1LA1LB_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ B C [1;1] [0;1] 2 1 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM12.

Module TM13.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC1LD_1RD---_1RE1LB_1LA1RF_1RC0RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ D E [1;1] [0;1] 5 26 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM13.

Module TM14.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD1LE_1RE---_1RA1LC_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ E A [1;1] [0;1] 5 12 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM14.

Module TM15.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LF_1LE1RA_1LF0LE_1LB1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2.nonhalt _ C D [1;1] [0;1] 5 26 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM15.

Module V2a.
Section V2a.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> [1;0;0] *> r.

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
  solve_rule ROv1.
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
  solve_rule ROv2.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2a.
End V2a.

Module TM19.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_0LF0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ B C [1;1] [0;1] 4 10 0).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM19.

Module TM20.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_0LE0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM20.

Module TM33.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0LB1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM33.

Module TM34.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_0LD1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2a.nonhalt _ B C [1;1] [0;1] 4 10 0).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM34.

Module V2b.
Section V2b.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 |> [1;0;0] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2+1) |> RC 1.
Proof.
  solve_rule ROv2.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2b.
End V2b.


Module TM21.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_0LE0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 7 71 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM21.

Module TM22.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_0LD0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 4 7 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM22.

Module TM23.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1LC0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 4 7 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM23.

Module TM24.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_1LB0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 7 71 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM24.

Module TM25.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1LE0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 4 7 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM25.

Module TM26.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_1LF0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 7 71 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM26.

Module TM29.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_0LD0LC_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 4 7 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM29.

Module TM30.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_0LE0LB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 7 71 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM30.

Module TM36.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_1LD1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ B C [1;1] [0;1] 7 71 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM36.

Module TM37.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1LB1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 4 7 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM37.

Module TM40.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RD_1LD1RF_1LE0LD_1RC1LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ E C [1;1] [0;1] 3 3 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM40.

Module TM41.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [1;1] [0;1] 5 11 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM41.

Module TM53.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1RE_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ F D [0;1] [0;1] 7 71 2).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM53.

Module TM54.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RD_1LD1RF_0LE0LD_1RE0RC_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ E C [0;1] [0;1] 3 3 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM54.

Module TM55.
Definition tm := Eval compute in (TM_from_str "1RB1RC_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ D B [0;1] [0;1] 4 9 2).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM55.

Module TM56.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2b.nonhalt _ C A [0;1] [0;1] 2 1 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM56.


Module V2c.
Section V2c.
Hypothesis tm:TM.
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis QL QR:Q.
Hypothesis qL qR:list Sym.
Hypothesis lenL0 k0 n0:nat.

Notation "l <| r" := (l <{{QL}} qL *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).

Definition LC0 len n := BinDec ld0 ld1 len n 0inf.
Definition LC1 len n := BinDec ld0 ld1 len n ldh.
Definition LC len n :=
  match len with
  | O => 0inf
  | S len =>
    if n <? 2^len then
      LC1 len n
    else
      LC0 len (n-2^len)
  end.

Lemma LC_mul2 len n:
  len<>O ->
  n<2^len ->
  LC (len+1) (n*2) = LC len n <* ld1.
Proof.
  intros.
  destruct len. 1: lia.
  unfold LC,LC0,LC1.
  cbn[Nat.pow] in *.
  cbn[Nat.add].
  destruct (Nat.ltb_spec n (2^len));
  destruct (Nat.ltb_spec (n*2) (2^(len+1)));
  rewrite Nat.pow_add_r in *; try lia.
  - rw_Bin.
    1: reflexivity.
    solve_pow2_lt.
  - replace (n*2-2^len*2^1) with ((n-2^len)*2) by lia.
    rw_Bin.
    1: reflexivity.
    solve_pow2_lt.
Qed.

Lemma LC_mul2add1 len n:
  len<>O ->
  n<2^len ->
  LC (len+1) (n*2+1) = LC len n <* ld0.
Proof.
  intros.
  destruct len. 1: lia.
  unfold LC,LC0,LC1.
  cbn[Nat.pow] in *.
  cbn[Nat.add].
  destruct (Nat.ltb_spec n (2^len));
  destruct (Nat.ltb_spec (n*2+1) (2^(len+1)));
  rewrite Nat.pow_add_r in *; try lia.
  - rw_Bin.
    1: reflexivity.
    solve_pow2_lt.
  - replace (n*2+1-2^len*2^1) with ((n-2^len)*2+1) by lia.
    rw_Bin.
    1: reflexivity.
    solve_pow2_lt.
Qed.

Lemma LC_0 len:
  len<>O ->
  LC len 0 = ldh <* ld1^^(len-1).
Proof.
  intros.
  destruct len. 1: lia.
  unfold LC,LC0,LC1.
  destruct (Nat.ltb_spec 0 (2^len)). 2: lia.
  replace (S len-1) with len by lia.
  rw_Bin; reflexivity.
Qed.

Lemma LC_full len:
  len<>O ->
  LC len (2^len-1) = 0inf <* ld0^^(len-1).
Proof.
  intros.
  destruct len. 1: lia.
  unfold LC,LC0,LC1.
  cbn[Nat.pow].
  destruct (Nat.ltb_spec (2*2^len-1) (2^len)). 1: lia.
  replace (S len-1) with len by lia.
  replace (2*2^len-1-2^len) with (2^len-1) by lia.
  rw_Bin; reflexivity.
Qed.

Lemma LC_mulpow2sub1 len k i:
  len<>O ->
  k<2^len ->
  LC (len+i) ((k+1)*2^i-1) =
  LC len k <* ld0^^i.
Proof.
  intros.
  induction i.
  - cbn; f_equal; lia.
  - replace (len+S i) with (len+i+1) by lia.
    replace ((k+1)*2^S i-1) with (((k+1)*2^i-1)*2+1) by (cbn; lia).
    rewrite LC_mul2add1 by solve_pow2_lt.
    rewrite IHi.
    reflexivity.
Qed.

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
  0inf <* ld0^^(n+1) |> [1] *> r.

Hypothesis LInc':
  forall r n,
  0inf <* ld1^^n <| r -->+
  ldh <* ld0^^n |> r.

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 |> [1;0;0] *> r.

Lemma LC_Inc len n r:
  1+n<2^len ->
  len<>O ->
  LC len (1+n) <| r -->+
  LC len n |> r.
Proof.
  intros.
  destruct len as [|len].
  1: lia.
  unfold LC.
  cbn[Nat.pow] in *.
  destruct (Nat.ltb_spec (1+n) (2^len));
  destruct (Nat.ltb_spec n (2^len)).
  - apply LBinDec_spec; try lia.
    follow' LInc.
  - lia.
  - replace (1+n-2^len) with O by lia.
    replace n with (2^len-1) by lia.
    unfold LC0,LC1.
    rw_Bin.
    follow' LInc'.
  - remember (n-2^len) as v1.
    replace (1+n-2^len) with (1+v1) by lia.
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

Lemma RC1_Ov lenL lenR k i m:
  lenL<>O ->
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC2 i ((2^i-1)*2) m.
Proof.
  intros.
  rewrite LC_mulpow2sub1 by solve_pow2_lt.
  rewrite LC_mul2 by solve_pow2_lt.
  solve_rule ROv1.
Qed.

Lemma RC1_Ov_0 lenL lenR k:
  lenL<>O ->
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  intros.
  rewrite LC_mulpow2sub1 by solve_pow2_lt.
  rewrite LC_mul2 by solve_pow2_lt.
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  lenL<>O ->
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  intros.
  rewrite LC_mul2add1 by solve_pow2_lt.
  rewrite LC_mulpow2sub1 by solve_pow2_lt.
  rewrite LC_mul2 by solve_pow2_lt.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  lenL<>O ->
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)-1))*2+1) |> RC 1.
Proof.
  intros.
  rewrite LC_mul2add1 by solve_pow2_lt.
  rewrite LC_mulpow2sub1 by solve_pow2_lt.
  rewrite LC_mul2 by solve_pow2_lt.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  lenL<>O ->
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2) n.
Proof.
  intros.
  rewrite LC_mul2add1 by lia.
  rewrite LC_0 by lia.
  rewrite LC_full by lia.
  destruct lenL as [|lenL]. 1: lia.
  replace (S lenL-1) with lenL by lia.
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
| cfgL lenL k n => lenL<>O /\ 2 <= k+n < 2^lenL
| cfgR lenL k n => lenL<>O /\ 2 <= k+n+1 < 2^lenL
| cfgL1 lenL k lenR n m => lenL<>O /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL<>O /\ n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=0 -> n=0 -> m=0 -> k+1 < 2^lenL)
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
    + lowbit_cases n.
      1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov; lia.
      repeat split; try lia.
      2,3: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2c.
End V2c.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LC_1LD1RF_1LE0LD_1LA0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F C [0;1] [0;1] 9 485 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0LF_1RD---_1RE1LE_1LA1RF_1RC0RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F E [0;1] [0;1] 5 25 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM2.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LD_1LE1RA_1LF0LE_1LB0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ A D [0;1] [0;1] 7 72 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM3.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD0LF_1RE---_1RA1LA_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F A [0;1] [0;1] 8 48 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM4.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC---_1RD1LD_1LF1RE_1RB0RD_1LA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ E D [0;1] [0;1] 5 12 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM5.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RC_1LD1RF_1LE0LD_1LA0LF_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F C [0;1] [0;1] 9 485 2).
  1-6: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC---_1RD0RD_1LE1RF_1LA0LE_1RB0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F D [0;1] [0;1] 5 12 1).
  1-6: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM7.

Module TM8.
Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0LF_1RD---_1RE0RE_1LA1RF_1RC0RE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F E [0;1] [0;1] 5 25 2).
  1-6: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM8.

Module TM9.
Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1LD0LF_1RE---_1RA0RA_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ F A [0;1] [0;1] 8 48 1).
  1-6: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM9.

Module TM10.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RD_1LE1RA_1LF0LE_1LB0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2c.nonhalt _ A D [0;1] [0;1] 7 72 1).
  1-6: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM10.


Module V2d.
Section V2d.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 <* ld1 |> [1] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2)*2) |> RC1 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2)*2) |> RC 1.
Proof.
  solve_rule ROv2.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3,4: intros; solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2d.
End V2d.

Module TM49.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RB_1LD1RF_0LE0LD_1RE0RC_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ E C [0;1] [0;1] 9 287 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM49.

Module TM50.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RC_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ F D [0;1] [0;1] 8 141 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM50.

Module TM51.
Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ D B [0;1] [0;1] 5 17 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM51.

Module TM52.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA0RF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [0;1] [0;1] 6 40 0).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM52.

Module TM135.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1RA1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM135.

Module TM142.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2d.nonhalt _ C A [1;1] [0;1] 8 89 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM142.


Module V2e.
Section V2e.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 <* ld0 |> [1] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2+1)*2+1) |> RC1 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2+1)*2+1) |> RC 1.
Proof.
  solve_rule ROv2.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        pose proof (Nat.mul_le_mono_pos_r (k*2+2) (2^lenL*2) (2^(lenR*2))).
        repeat split; try lia.
        2,3,4: intros; solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2e.
End V2e.

Module TM136.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_1RD1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ B C [1;1] [0;1] 10 543 2).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM136.

Module TM137.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1RB1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM137.

Module TM138.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_0RC1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ B C [1;1] [0;1] 10 543 2).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM138.

Module TM139.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0RA1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM139.

Module TM140.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RF_1LD1RE_1LB0LD_1RA0RC_0RC0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ B C [1;1] [0;1] 10 543 2).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM140.

Module TM141.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0RA0LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2e.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM141.


Module V2f.
Section V2f.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 <* ld1 |> [1] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2+1)*2) |> RC1 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1+1) (((((k*2+1)*2^(lenR*2)-1))*2+1)*2) |> RC 1.
Proof.
  solve_rule ROv2.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR1 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        pose proof (Nat.mul_le_mono_pos_r (k*2+2) (2^lenL*2) (2^(lenR*2))).
        repeat split; try lia.
        2,3,4: intros; solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2f.
End V2f.

Module TM129.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_0RC0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ B C [1;1] [0;1] 8 144 0).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM129.

Module TM130.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_1LC0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ B C [1;1] [0;1] 8 144 0).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM130.

Module TM131.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RF_1LD1RE_1LB0LD_1RA0RC_1RD0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ B C [1;1] [0;1] 8 144 0).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM131.

Module TM132.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_0RA0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM132.

Module TM133.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1LA0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM133.

Module TM134.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RB0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2f.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es_r.
  1: esx.
  1: cbn; lia.
Qed.
End TM134.


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

Hypothesis LOv:
  forall r n,
  ldh <* ld1^^n <| r -->+
  ldh <* ld0^^(n+1) |> [1] *> r.

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2_O:
  forall l r,
  l |> rd1^^0 *> rm3 *> r -->+
  l <* ld1 <* ld0 |> [1;0;0] *> r.

Hypothesis ROv2_S:
  forall l r n,
  l |> rd1^^(1+n) *> rm3 *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) <* ld0 <* ld1 |> [1;0;0] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov_S lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 (1+lenR) 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1+lenR*2+1+1) (((((k*2+1)*2+1)*2^(lenR*2)-1)*2+1)*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC2_Ov_S_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 (1+lenR) 0 0 -->+
  LC (lenL+1+1+lenR*2+1+1) (((((k*2+1)*2+1)*2^(lenR*2)-1)*2+1)*2) |> RC 1.
Proof.
  solve_rule ROv2_S.
Qed.

Lemma RC2_Ov_O lenL k i m:
  k<2^lenL ->
  LC lenL k |> RC2 0 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma RC2_Ov_O_0 lenL k:
  k<2^lenL ->
  LC lenL k |> RC2 0 0 0 -->+
  LC (lenL+1+1) ((k*2)*2+1) |> RC 1.
Proof.
  solve_rule ROv2_O.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC (lenL+1) ((2^lenL-1)*2+1) |> RC1 i ((2^i-1)*2) n.
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
      eexists (cfgR1 _ _ _ _ _). split.
      1: apply LC_Ov.
      repeat split; try lia.
      2,3: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
        lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m;
      destruct lenR as [|lenR].
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_O_0; lia.
        repeat split; try lia.
        solve_pow2_lt.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_S_0; lia.
        repeat split; try lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_O; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        lia.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov_S; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V1a.
End V1a.

Module TM127.
Definition tm := Eval compute in (TM_from_str "1LB1RC_0LC0LB_1RD0RA_1RE---_1RA1LF_1LD1LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ E A [1;1;1;1] [0;1;0;1] 5 27 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM127.

Module TM128.
Definition tm := Eval compute in (TM_from_str "1LB1LC_1RC---_1RD1LA_1LF1RE_1RB0RD_0LE0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V1a.nonhalt _ C D [1;1;1;1] [0;1;0;1] 5 27 0).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM128.


Module V2h.
Section V2h.
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

Hypothesis ROv1:
  forall l r n,
  l |> rd1^^n *> rm1 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n,
  l |> rd1^^n *> rm3 *> r -->+
  l <* ld0 <* ld1^^(n*2) <* ld1 |> [1;0;0] *> r.

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
  solve_rule ROv1.
Qed.

Lemma RC2_Ov lenL lenR k i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i) -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)))*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC (lenL+1+lenR*2+1) ((((k*2+1)*2^(lenR*2)))*2) |> RC 1.
Proof.
  solve_rule ROv2.
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
| cfgR2 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=0 -> n=0 -> m=0 -> k+1 < 2^lenL)
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
      repeat split; try lia.
      2: solve_pow2_lt.
      pose proof (split_bound_v1 x i lenL).
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
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC1_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
           lia.
        -- intros; subst.
           pose proof (Nat.mul_le_mono_pos_r (k*2+2) (2^lenL*2) (2^(lenR*2))).
           solve_pow2_lt.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbit_cases m.
      * eexists (cfgR _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        2: intros; subst; solve_pow2_lt.
        pose proof (split_bound_v2 x i).
        pose proof (Nat.le_mul_r (k*2+1) (2^(lenR*2))).
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

End V2h.
End V2h.

Module TM18.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1LD0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2h.nonhalt _ C A [1;1] [0;1] 4 10 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM18.


