From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
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

Module V2g.
Section V2g.
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
  l <| rd0^^(n+1) *> [1;0;0] *> r.

Hypothesis LOv':
  forall r n,
  ldh <* ld1^^n <| [1] *> r -->+
  ldh <* ld0^^(n+1) |> r.

Hypothesis ROv':
  forall l r n,
  l |> rd1^^n *> [1;0;0;1;1] *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 |> [1] *> r.

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
  LC lenL k <| RC2 (i+1+lenR) ((((2^i-1)*2+1)*2^lenR-1)*2+1) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC lenL k <| RC (2^lenR*2).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1]*>0inf).

Lemma LC_Ov1 lenL lenR:
  LC (lenL) O <| RC1 (lenR+1+1) (((2^lenR-1)*2+1)*2) 0 -->+
  LC (lenL+1) ((2^(lenL)-1)*2+1) |> RC' (lenR+1) (((2^lenR-1)*2+1)*2+1).
Proof.
  unfold LC,RC1,RC'.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv'.
  rewrite (Nat.add_comm lenR 1).
  replace (2^lenR-1) with ((0*2+1)*2^lenR-1) by lia.
  rw_Bin.
  2,3: solve_pow2_lt.
  simpl_rotate; simpl_tape; finish.
Qed.

Lemma RC'_Ov lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2+1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'.
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

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

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

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  induction n; intros.
  1: finish.
  follow100 RC'_Inc.
  replace (k+S n) with (1+(k+n)) by lia.
  follow100 LC_Inc.
  follow IHn.
  1,2: lia.
  finish.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Lemma corner_case lenL:
  LC (lenL+2) O <| RC (2^(lenL+2)) -->+
  LC (lenL + 1 + 1 + 1 + 1 + (lenL + 1) * 2 + 1)
    (((2 ^ lenL * 2 * 2 * 2 + 1) * 2 ^ ((lenL + 1) * 2) - 1) * 2 + 1) |> RC 1.
Proof.
  replace (2^(lenL+2)) with ((0*2+1)*2^(lenL+2)) by lia.
  follow10 LC_Ov.
  replace ((2^(lenL+2)-1)*2) with (((2^lenL-1)*2+1)*2+(2^(lenL+2)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  replace (lenL+2) with (lenL+1+1) by lia.
  follow100 LC_Ov1.
  replace ((2 ^ (lenL + 1 + 1) - 1) * 2 + 1) with (2^(lenL)*2*2+(((2 ^ lenL - 1) * 2 + 1) * 2 + 1)) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  follow100 RC'_Ov.
  1: lia'.
  finish.
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
| cfgL lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgL1 lenL k lenR n m => lenL>=2 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL>=2 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgL2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*2 < n+2^lenL*2)
| cfgR2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*2+1 < n+2^lenL*2)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct (Nat.eqb_spec n (2^lenL)) as [E|E].
      * subst n.
        remember (lenL-2) as lenL'.
        replace lenL with (lenL'+2) in * by lia.
        clear HeqlenL'.
        eexists (cfgR _ _ _). split.
        1: apply corner_case.
        replace ((lenL'+1)*2) with (lenL'*2+2) by lia.
        pose proof (Nat.le_mul_r (2^(lenL'*2)) (2^(lenL'))).
        lia'.
      * lowbit_cases n.
        1: lia.
        eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        pose proof (split_bound_v3 x i lenL).
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
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           zify_le_mul_r; lia.
        -- intros; subst x.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
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
      * eexists (cfgL _ _ _). split.
        1: apply RC2_Ov_0; lia.
        lia.
      * eexists (cfgL2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        assert (
        (((2 ^ i - 1) * 2 + 1) * 2 ^ lenR - 1) * 2 + 1 <
        2^(i+1+lenR+1)) as E by solve_pow2_lt.
        gen E.
        lia'.
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

End V2g.
End V2g.


Module TM16.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1LB0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2g.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM16.

Module TM35.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0LC1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2g.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM35.


Module V2ga.
Section V2ga.
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
  l <| rd0^^(n+1) *> [1;0;0] *> r.

Hypothesis LOv':
  forall r n,
  ldh <* ld1^^n <| [1] *> r -->+
  ldh <* ld0^^(n+1) |> r.

Hypothesis ROv':
  forall l n,
  l |> rd1^^n *> [1;0;0;1;1] *> 0inf -->+
  l <| rd0^^(2+n) *> rd1 *> 0inf.

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
  LC lenL k <| RC2 (i+1+lenR) ((((2^i-1)*2+1)*2^lenR-1)*2+1) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC lenL k <| RC (2^lenR*2).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1]*>0inf).

Lemma LC_Ov1 lenL lenR:
  LC (lenL) O <| RC1 (lenR+1+1) (((2^lenR-1)*2+1)*2) 0 -->+
  LC (lenL+1) ((2^(lenL)-1)*2+1) |> RC' (lenR+1) (((2^lenR-1)*2+1)*2+1).
Proof.
  unfold LC,RC1,RC'.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv'.
  rewrite (Nat.add_comm lenR 1).
  replace (2^lenR-1) with ((0*2+1)*2^lenR-1) by lia.
  rw_Bin.
  2,3: solve_pow2_lt.
  simpl_rotate; simpl_tape; finish.
Qed.

Lemma RC'_Ov l lenR:
  l |> RC' lenR 0 -->+
  l <| RC (2^(2+lenR)).
Proof.
  unfold RC'.
  solve_rule ROv'.
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

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

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

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  induction n; intros.
  1: finish.
  follow100 RC'_Inc.
  replace (k+S n) with (1+(k+n)) by lia.
  follow100 LC_Inc.
  follow IHn.
  1,2: lia.
  finish.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Lemma corner_case lenL:
  LC (lenL+2) O <| RC (2^(lenL+2)) -->+
  LC (lenL + 1 + 1 + 1) (2 ^ lenL * 2 * 2) <| RC (2 ^ (lenL + 3)).
Proof.
  replace (2^(lenL+2)) with ((0*2+1)*2^(lenL+2)) by lia.
  follow10 LC_Ov.
  replace ((2^(lenL+2)-1)*2) with (((2^lenL-1)*2+1)*2+(2^(lenL+2)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  replace (lenL+2) with (lenL+1+1) by lia.
  follow100 LC_Ov1.
  replace ((2 ^ (lenL + 1 + 1) - 1) * 2 + 1) with (2^(lenL)*2*2+(((2 ^ lenL - 1) * 2 + 1) * 2 + 1)) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  follow100 RC'_Ov.
  finish.
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
| cfgL lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgL1 lenL k lenR n m => lenL>=2 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL>=2 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgL2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*2 < n+2^lenL*2)
| cfgR2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*2+1 < n+2^lenL*2)
end.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct (Nat.eqb_spec n (2^lenL)) as [E|E].
      * subst n.
        remember (lenL-2) as lenL'.
        replace lenL with (lenL'+2) in * by lia.
        clear HeqlenL'.
        eexists (cfgL _ _ _). split.
        1: apply corner_case.
        lia'.
      * lowbit_cases n.
        1: lia.
        eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        pose proof (split_bound_v3 x i lenL).
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
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           zify_le_mul_r; lia.
        -- intros; subst x.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
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
      * eexists (cfgL _ _ _). split.
        1: apply RC2_Ov_0; lia.
        lia.
      * eexists (cfgL2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        assert (
        (((2 ^ i - 1) * 2 + 1) * 2 ^ lenR - 1) * 2 + 1 <
        2^(i+1+lenR+1)) as E by solve_pow2_lt.
        gen E.
        lia'.
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

End V2ga.
End V2ga.

Module TM38.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ga.nonhalt _ C A [1;1] [0;1] 5 11 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM38.

Module TM59.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ga.nonhalt _ C A [0;1] [0;1] 2 0 6).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM59.

Module TM60.
Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ga.nonhalt _ D B [0;1] [0;1] 2 0 4).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM60.

Module TM61.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1RD_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V2ga.nonhalt _ F D [0;1] [0;1] 2 0 5).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM61.


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

Definition RC3 len n m := BinDec2 [0] [1] [0;0;0] len n ([1;0] *> BinInc rd1 m). 

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
  l <| rd0^^(n+1) *> [0;1;0] *> r.

Hypothesis ROv3:
  forall l r n,
  l |> rd1^^n *> [1;1;0] *> rd1 *> r -->+
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

Lemma RC3_Inc len n m l:
  1+n<2^(len+1) ->
  l |> RC3 len (1+n) m -->+
  l <| RC3 len n m.
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

Lemma RC2_Ov l lenR m:
  l |> RC2 lenR 0 m -->+
  l <| RC3 (lenR+1) (((2^lenR-1)*2+1)*2+1) m.
Proof.
  unfold RC3.
  solve_rule ROv2.
Qed.

Lemma RC3_Ov_0 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 ((m*2+1)*2^i*2) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC1 (i+1) (((2^i-1)*2+1)*2) m.
Proof.
  unfold RC3.
  solve_rule ROv1.
Qed.

Lemma RC3_Ov_0_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 (0*2) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC 1.
Proof.
  epose proof (ROv1 _ 0inf _) as I1.
  cbn[Str_app] in I1.
  do 2 rewrite <-(const_unfold _ 0) in I1.
  unfold RC3.
  solve_rule I1.
Qed.

Lemma RC3_Ov_1 lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 ((m*2+1)*2^i*2+1) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2) |> RC2 i ((2^i-1)*2) m.
Proof.
  unfold RC3.
  solve_rule ROv3.
Qed.

Lemma RC3_Ov_1_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC3 lenR 0 (0*2+1) -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2) |> RC 1.
Proof.
  unfold RC3.
  solve_rule ROv3.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try assumption; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.


Close Scope sym.

Inductive Config :=
| cfgL(lenL k n:nat)
| cfgR(lenL k n:nat)
| cfgR1_S(lenL k lenR n i m:nat)
| cfgR1_O(lenL k lenR n:nat)
| cfgR2(lenL k lenR n m:nat)
| cfgR3(lenL k lenR n m:nat)
.

Definition to_config(x:Config):=
match x with
| cfgL lenL k n => LC lenL k <| RC n
| cfgR lenL k n => LC lenL k |> RC n
| cfgR1_S lenL k lenR n i m => LC lenL k |> RC1 lenR n ((m*2+1)*2^i)
| cfgR1_O lenL k lenR n => LC lenL k |> RC1 lenR n 0
| cfgR2 lenL k lenR n m => LC lenL k |> RC2 lenR n m
| cfgR3 lenL k lenR n m => LC lenL k |> RC3 lenR n m
end.

Definition P(x:Config):Prop :=
match x with
| cfgL lenL k n => 2 <= k+n < 2^lenL
| cfgR lenL k n => 2 <= k+n+1 < 2^lenL
| cfgR1_O lenL k lenR n =>
  n <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n+2^lenL<>k+1)
| cfgR1_S lenL k lenR n i m =>
  n+(m*2+1)*2^i <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n*2+m+2^i*6 <= k*2+2)
| cfgR2 lenL k lenR n m => n+m+2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) 
| cfgR3 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1<>2^lenL)
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
      lowbit_cases x.
      * eexists (cfgR1_O _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        destruct lenL.
        -- lia.
        -- pose proof (Nat.pow_lt_mono_r_iff 2 i (S lenL)).
           pose proof (Nat.pow_le_mono_r_iff 2 i (lenL)).
           cbn; lia.
      * eexists (cfgR1_S _ _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        -- remember ((x0*2+1)*2^i0) as v1.
           pose proof (split_bound_v1 v1 i lenL).
           lia.
        -- intro; subst i.
           cbn in *.
           destruct lenL.
           1: lia.
           cbn[Nat.pow] in *.
           pose proof (split_bound_v1 x0 i0 lenL).
           lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1_S _ _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply RC1_Ov; lia.
    repeat split; try lia.
    2,3: solve_pow2_lt.
    destruct lenR.
    1: lia.
    replace (S lenR*2) with (lenR*2+2) by lia.
    solve_pow2_lt.
    zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1_O _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    eexists (cfgR _ _ _). split.
    1: apply RC1_Ov_0; lia.
    repeat split; try lia.
    destruct lenR as [|lenR].
    1: solve_pow2_lt.
    replace (S lenR*2) with (lenR*2+2) by lia.
    pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
    solve_pow2_lt.
  - destruct k. 1: lia.
    destruct n.
    2: {
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    eexists (cfgR3 _ _ _ _ _). split.
    1: follow10 RC2_Ov; follow100 LC_Inc; finish.
    repeat split; try lia.
    solve_pow2_lt.
  - destruct n.
    2: {
      destruct k. 1: lia.
      eexists (cfgR3 _ _ _ _ _). split.
      1: follow10 RC3_Inc; follow100 LC_Inc; finish.
      lia.
    }
    remember (m/2) as m1.
    remember (m mod 2) as m2.
    replace m with (m1*2+m2) in * by lia.
    destruct m2 as [|[|]]. 3: lia.
    + rewrite Nat.add_0_r in *.
      lowbit_cases m1.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_0_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * lowbit_cases x.
        -- eexists (cfgR1_O _ _ _ _). split.
           1: apply RC3_Ov_0; lia.
           repeat split; try lia.
           2,3: solve_pow2_lt.
           zify_le_mul_r; lia.
        -- eexists (cfgR1_S _ _ _ _ _ _). split.
           1: apply RC3_Ov_0; lia.
           repeat split; try lia.
           2,3: solve_pow2_lt.
           remember ((x0*2+1)*2^i0) as v1.
           pose proof (split_bound_v2 v1 i).
           zify_le_mul_r; lia.
    + lowbit_cases m1.
      * eexists (cfgR _ _ _). split.
        1: apply RC3_Ov_1_0; lia.
        repeat split; try lia.
        destruct lenR as [|lenR].
        1: solve_pow2_lt.
        replace (S lenR*2) with (lenR*2+2) by lia.
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        solve_pow2_lt.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC3_Ov_1; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
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

Module TM27.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RA1LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ E A [1;1] [0;1] 4 9 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM27.

Module TM28.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RA0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM28.

Module TM32.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0LF1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM32.

Module TM39.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1RF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 6 23 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM39.

Module TM42.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM42.

Module TM43.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_0LF1RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM43.

Module TM44.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1LF---_1RA1RF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [1;1] [0;1] 6 23 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM44.

Module TM45.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1RF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [0;1] [0;1] 6 23 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM45.

Module TM46.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1RC_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ F D [0;1] [0;1] 8 46 4).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM46.

Module TM47.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [0;1] [0;1] 5 10 4).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM47.

Module TM48.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1RB_1LD1RF_0LE0LD_1RE0RC_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ E C [0;1] [0;1] 9 95 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM48.

Module TM62.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1LA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ D B [0;1] [0;1] 5 10 4).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM62.

Module TM63.
Definition tm := Eval compute in (TM_from_str "1LB---_1RC1RB_1LE1RD_1RA0RC_0LF0LE_1RF0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ F C [0;1] [0;1] 11 190 4).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM63.

Module TM64.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1LF---_1RA1RF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [0;1] [0;1] 6 23 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM64.

Module TM65.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC---_1RD1RC_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ F D [0;1] [0;1] 8 46 4).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM65.

Module TM66.
Definition tm := Eval compute in (TM_from_str "1LB1RF_0LC0LB_0RD0RA_1LE---_1RA1RE_1RD0RA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V3.nonhalt _ C A [0;1] [0;1] 6 23 1).
  1-6: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM66.


Module V7.
Section V7.
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
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0;0] *> r.

Hypothesis LOv':
  forall r n,
  ldh <* ld1^^n <| [1] *> r -->+
  ldh <* ld0^^(n+1) |> r.

Hypothesis ROv':
  forall l r n,
  l |> rd1^^n *> [1;0;0;1;1] *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld0 |> [1] *> r.

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

Lemma RC2_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC lenL k <| RC2 (i0+1+(lenR+i+1)) ((((2^i0-1)*2+1)*2^(lenR+i+1)-1)*2+1) m.
Proof.
  solve_rule ROv2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC lenL k <| RC (2^(lenR+i+2)).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1]*>0inf).

Lemma LC_Ov1 lenL lenR:
  LC (lenL) O <| RC1 (lenR+1+1) (((2^lenR-1)*2+1)*2) 0 -->+
  LC (lenL+1) ((2^(lenL)-1)*2+1) |> RC' (lenR+1) (((2^lenR-1)*2+1)*2+1).
Proof.
  unfold LC,RC1,RC'.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv'.
  rewrite (Nat.add_comm lenR 1).
  replace (2^lenR-1) with ((0*2+1)*2^lenR-1) by lia.
  rw_Bin.
  2,3: solve_pow2_lt.
  simpl_rotate; simpl_tape; finish.
Qed.

Lemma RC'_Ov lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2+1) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'.
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

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

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

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  induction n; intros.
  1: finish.
  follow100 RC'_Inc.
  replace (k+S n) with (1+(k+n)) by lia.
  follow100 LC_Inc.
  follow IHn.
  1,2: lia.
  finish.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Lemma corner_case lenL:
  LC (lenL+2) O <| RC (2^(lenL+2)) -->+
  LC (lenL + 1 + 1 + 1 + 1 + (lenL + 1) * 2 + 1)
    (((2 ^ lenL * 2 * 2 * 2 + 1) * 2 ^ ((lenL + 1) * 2) - 1) * 2 + 1) |> RC 1.
Proof.
  replace (2^(lenL+2)) with ((0*2+1)*2^(lenL+2)) by lia.
  follow10 LC_Ov.
  replace ((2^(lenL+2)-1)*2) with (((2^lenL-1)*2+1)*2+(2^(lenL+2)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  replace (lenL+2) with (lenL+1+1) by lia.
  follow100 LC_Ov1.
  replace ((2 ^ (lenL + 1 + 1) - 1) * 2 + 1) with (2^(lenL)*2*2+(((2 ^ lenL - 1) * 2 + 1) * 2 + 1)) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  follow100 RC'_Ov.
  1: lia'.
  finish.
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
| cfgL lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgL1 lenL k lenR n m => lenL>=2 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL>=2 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgL2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4 < n+2^lenL*2)
| cfgR2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4+1 < n+2^lenL*2)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct (Nat.eqb_spec n (2^lenL)) as [E|E].
      * subst n.
        remember (lenL-2) as lenL'.
        replace lenL with (lenL'+2) in * by lia.
        clear HeqlenL'.
        eexists (cfgR _ _ _). split.
        1: apply corner_case.
        replace ((lenL'+1)*2) with (lenL'*2+2) by lia.
        pose proof (Nat.le_mul_r (2^(lenL'*2)) (2^(lenL'))).
        lia'.
      * lowbit_cases n.
        1: lia.
        eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        pose proof (split_bound_v3 x i lenL).
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
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           zify_le_mul_r; lia.
        -- intros; subst x.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
           pp_pow2_lt_le i lenL.
           remember (lenR*2) as lenR2.
           zify_pow2sub1; lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia'.
        destruct i.
        1: lia'.
        pp_pow2_lt_le (i+lenR+2) lenL.
        cbn[Nat.pow] in *.
        pose proof (Nat.mul_le_mono_pos_r (2^i) (2^i*2-1) (2^lenR)).
        lia.
      * eexists (cfgL2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2: solve_pow2_lt.
        -- repeat rewrite Nat.pow_add_r in *.
           zify_pow2sub1; lia.
        -- intro; subst.
           pp_pow2_lt_le (i0+i+lenR+3) lenL.
           zify_pow2sub1; lia.
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

End V7.
End V7.

Module TM163.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1LC1LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM163.

Module TM164.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_1RD0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM164.

Module TM167.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_1LC1LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM167.

Module TM168.
Definition tm := Eval compute in (TM_from_str "1LB0LF_1RC0RA_1LA1RD_1RE0RC_1RB---_0RC0LA").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ B C [1;1] [0;1] 5 9 8).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM168.

Module TM169.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RB_1RF0RA_0RA0LB_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM169.

Module TM170.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RE_1LE1RA_1LC0LF_0RD0LE").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ C D [1;1] [0;1] 5 11 2).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM170.

Module TM171.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RD_1LD1RF_1LB0LE_0RC0LD_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7.nonhalt _ B C [1;1] [0;1] 4 9 4).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM171.

Module V7a.
Section V7a.
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
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0;0] *> r.

Hypothesis LOv':
  forall r n,
  ldh <* ld1^^n <| [1] *> r -->+
  ldh <* ld0^^(n+1) |> r.

Hypothesis ROv':
  forall l r n,
  l |> rd1^^n *> [1;0;0;1;1] *> r -->+
  l <* ld0 <* ld1 <* ld0^^(n*2) |> [1] *> r.

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

Lemma RC2_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC lenL k <| RC2 (i0+1+(lenR+i+1)) ((((2^i0-1)*2+1)*2^(lenR+i+1)-1)*2+1) m.
Proof.
  solve_rule ROv2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC lenL k <| RC (2^(lenR+i+2)).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1]*>0inf).

Lemma LC_Ov1 lenL lenR:
  LC (lenL) O <| RC1 (lenR+1+1) (((2^lenR-1)*2+1)*2) 0 -->+
  LC (lenL+1) ((2^(lenL)-1)*2+1) |> RC' (lenR+1) (((2^lenR-1)*2+1)*2+1).
Proof.
  unfold LC,RC1,RC'.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv'.
  rewrite (Nat.add_comm lenR 1).
  replace (2^lenR-1) with ((0*2+1)*2^lenR-1) by lia.
  rw_Bin.
  2,3: solve_pow2_lt.
  simpl_rotate; simpl_tape; finish.
Qed.

Lemma RC'_Ov lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 -->+
  LC (lenL+1+1+lenR*2) ((((k*2+1)*2+1)*2^(lenR*2)-1)) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'.
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

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

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

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  induction n; intros.
  1: finish.
  follow100 RC'_Inc.
  replace (k+S n) with (1+(k+n)) by lia.
  follow100 LC_Inc.
  follow IHn.
  1,2: lia.
  finish.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Lemma corner_case lenL:
  LC (lenL+2) O <| RC (2^(lenL+2)) -->+
  LC (lenL + 1 + 1 + 1 + 1 + 1 + (lenL + 1) * 2)
    (((2 ^ lenL * 2 * 2 * 2 + 1) * 2 + 1) * 2 ^ ((lenL + 1) * 2) - 1) |> RC 1.
Proof.
  replace (2^(lenL+2)) with ((0*2+1)*2^(lenL+2)) by lia.
  follow10 LC_Ov.
  replace ((2^(lenL+2)-1)*2) with (((2^lenL-1)*2+1)*2+(2^(lenL+2)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  replace (lenL+2) with (lenL+1+1) by lia.
  follow100 LC_Ov1.
  replace ((2 ^ (lenL + 1 + 1) - 1) * 2 + 1) with (2^(lenL)*2*2+(((2 ^ lenL - 1) * 2 + 1) * 2 + 1)) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  follow100 RC'_Ov.
  1: lia'.
  finish.
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
| cfgL lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgL1 lenL k lenR n m => lenL>=2 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL>=2 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgL2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4 < n+2^lenL*2)
| cfgR2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4+1 < n+2^lenL*2)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct (Nat.eqb_spec n (2^lenL)) as [E|E].
      * subst n.
        remember (lenL-2) as lenL'.
        replace lenL with (lenL'+2) in * by lia.
        clear HeqlenL'.
        eexists (cfgR _ _ _). split.
        1: apply corner_case.
        replace ((lenL'+1)*2) with (lenL'*2+2) by lia.
        pose proof (Nat.le_mul_r (2^(lenL'*2)) (2^(lenL'))).
        lia'.
      * lowbit_cases n.
        1: lia.
        eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        pose proof (split_bound_v3 x i lenL).
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
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           zify_le_mul_r; lia.
        -- intros; subst x.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
           pp_pow2_lt_le i lenL.
           remember (lenR*2) as lenR2.
           zify_pow2sub1; lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia'.
        destruct i.
        1: lia'.
        pp_pow2_lt_le (i+lenR+2) lenL.
        cbn[Nat.pow] in *.
        pose proof (Nat.mul_le_mono_pos_r (2^i) (2^i*2-1) (2^lenR)).
        lia.
      * eexists (cfgL2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2: solve_pow2_lt.
        -- repeat rewrite Nat.pow_add_r in *.
           zify_pow2sub1; lia.
        -- intro; subst.
           pp_pow2_lt_le (i0+i+lenR+3) lenL.
           zify_pow2sub1; lia.
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

End V7a.
End V7a.

Module TM161.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1LC1RE_1LD0LC_1LA1LD_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7a.nonhalt _ A B [1;1;1;1] [0;1;0;1] 4 11 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM161.

Module TM162.
Definition tm := Eval compute in (TM_from_str "1LB1RE_1LC0LB_1LD1LC_1RA0RC_1RF0RA_1RD---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7a.nonhalt _ D A [1;1;1;1] [0;1;0;1] 5 9 8).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM162.

Module V7b.
Section V7b.
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
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0;0] *> r.

Hypothesis LOv':
  forall r n,
  ldh <* ld1^^n <| [1] *> r -->+
  ldh <* ld0^^(n+1) |> r.

Hypothesis ROv':
  forall l r n,
  l |> rd1^^n *> [1;0;0;1;1] *> r -->+
  l <* ld1 <* ld0^^(n*2) <* ld1 |> [1] *> r.

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

Lemma RC2_Ov lenL lenR k i i0 m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC lenL k <| RC2 (i0+1+(lenR+i+1)) ((((2^i0-1)*2+1)*2^(lenR+i+1)-1)*2+1) m.
Proof.
  solve_rule ROv2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC lenL k <| RC (2^(lenR+i+2)).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Definition RC' len n := BinDec2 [0] [1] [0;0;0] len n ([0;0;1;1]*>0inf).

Lemma LC_Ov1 lenL lenR:
  LC (lenL) O <| RC1 (lenR+1+1) (((2^lenR-1)*2+1)*2) 0 -->+
  LC (lenL+1) ((2^(lenL)-1)*2+1) |> RC' (lenR+1) (((2^lenR-1)*2+1)*2+1).
Proof.
  unfold LC,RC1,RC'.
  rw_Bin.
  2,3: solve_pow2_lt.
  follow10 LOv'.
  rewrite (Nat.add_comm lenR 1).
  replace (2^lenR-1) with ((0*2+1)*2^lenR-1) by lia.
  rw_Bin.
  2,3: solve_pow2_lt.
  simpl_rotate; simpl_tape; finish.
Qed.

Lemma RC'_Ov lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC' lenR 0 -->+
  LC (lenL+1+lenR*2+1) (((k*2+1)*2^(lenR*2)-1)*2) |> RC 1.
Proof.
  unfold RC'.
  solve_rule ROv'.
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

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

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

Lemma RC'_Incs lenL k lenR n:
  k+n<2^lenL ->
  n<2^(lenR+1) ->
  LC lenL (k+n) |> RC' lenR n -->*
  LC lenL k |> RC' lenR 0.
Proof.
  induction n; intros.
  1: finish.
  follow100 RC'_Inc.
  replace (k+S n) with (1+(k+n)) by lia.
  follow100 LC_Inc.
  follow IHn.
  1,2: lia.
  finish.
Qed.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

Lemma corner_case lenL:
  LC (lenL+2) O <| RC (2^(lenL+2)) -->+
  LC (lenL + 1 + 1 + 1 + 1 + (lenL + 1) * 2 + 1)
    (((2 ^ lenL * 2 * 2 * 2 + 1) * 2 ^ ((lenL + 1) * 2) - 1) * 2) |> RC 1.
Proof.
  replace (2^(lenL+2)) with ((0*2+1)*2^(lenL+2)) by lia.
  follow10 LC_Ov.
  replace ((2^(lenL+2)-1)*2) with (((2^lenL-1)*2+1)*2+(2^(lenL+2)-1)+1) by lia'.
  follow RC1_Incs.
  1,2: lia'.
  replace (lenL+2) with (lenL+1+1) by lia.
  follow100 LC_Ov1.
  replace ((2 ^ (lenL + 1 + 1) - 1) * 2 + 1) with (2^(lenL)*2*2+(((2 ^ lenL - 1) * 2 + 1) * 2 + 1)) by lia'.
  follow RC'_Incs.
  1,2: lia'.
  follow100 RC'_Ov.
  1: lia'.
  finish.
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
| cfgL lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=2 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgL1 lenL k lenR n m => lenL>=2 /\ n+m+1 <= k < 2^lenL /\ n<2^(lenR+1)
| cfgR1 lenL k lenR n m => lenL>=2 /\ n+m <= k < 2^lenL /\ n<2^(lenR+1)
| cfgL2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4 < n+2^lenL*2)
| cfgR2 lenL k lenR n m => lenL>=2 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4+1 < n+2^lenL*2)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct (Nat.eqb_spec n (2^lenL)) as [E|E].
      * subst n.
        remember (lenL-2) as lenL'.
        replace lenL with (lenL'+2) in * by lia.
        clear HeqlenL'.
        eexists (cfgR _ _ _). split.
        1: apply corner_case.
        replace ((lenL'+1)*2) with (lenL'*2+2) by lia.
        pose proof (Nat.le_mul_r (2^(lenL'*2)) (2^(lenL'))).
        lia'.
      * lowbit_cases n.
        1: lia.
        eexists (cfgR1 _ _ _ _ _). split.
        1: apply LC_Ov.
        repeat split; try lia.
        2: solve_pow2_lt.
        pose proof (split_bound_v3 x i lenL).
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
        pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: apply RC1_Ov; lia.
        repeat split; try lia.
        2,3: solve_pow2_lt.
        -- pose proof (split_bound_v2 x i).
           zify_le_mul_r; lia.
        -- intros; subst x.
           pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
           pp_pow2_lt_le i lenL.
           remember (lenR*2) as lenR2.
           zify_pow2sub1; lia.
    + eexists (cfgL1 _ _ _ _ _). split.
      1: apply RC1_Inc; lia.
      lia.
  - destruct k as [|k].
    1: lia.
    eexists (cfgR2 _ _ _ _ _). split.
    1: apply LC_Inc; lia.
    lia.
  - destruct n as [|n].
    + lowbitS_cases m.
      lowbit_cases x.
      * eexists (cfgL _ _ _). split.
        1: apply RC2_Ov_0; lia.
        repeat split; try lia'.
        destruct i.
        1: lia'.
        pp_pow2_lt_le (i+lenR+2) lenL.
        cbn[Nat.pow] in *.
        pose proof (Nat.mul_le_mono_pos_r (2^i) (2^i*2-1) (2^lenR)).
        lia.
      * eexists (cfgL2 _ _ _ _ _). split.
        1: apply RC2_Ov; lia.
        repeat split; try lia.
        2: solve_pow2_lt.
        -- repeat rewrite Nat.pow_add_r in *.
           zify_pow2sub1; lia.
        -- intro; subst.
           pp_pow2_lt_le (i0+i+lenR+3) lenL.
           zify_pow2sub1; lia.
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

End V7b.
End V7b.

Module TM174.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA0RB").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7b.nonhalt _ C A [1;1] [0;1] 4 9 1).
  1-7: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM174.

Module V8.
Section V8.
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
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(n*2) |> rd1 *> rd0^^m *> [0;1;0;0;0] *> r.

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

Lemma RC2_Ov lenL k lenR i m:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((m*2+1)*2^i-1) -->+
  LC (lenL+1+lenR*2) ((k*2+1)*2^(lenR*2)-1) |> RC1 (i+1) (((2^i-1)*2+1)*2) m.
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try assumption; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.


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
| cfgR1 lenL k lenR n m =>
  n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1<>2^lenL)
| cfgR2 lenL k lenR n m =>
  n+m*2+1 <= k < 2^lenL /\ n<2^(lenR+1) 
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
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbit_cases m.
    + eexists (cfgR _ _ _). split.
      1: apply RC1_Ov_0; lia.
      repeat split; try lia.
      destruct lenR as [|lenR].
      1: solve_pow2_lt.
      replace (S lenR*2) with (lenR*2+2) by lia.
      pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
      solve_pow2_lt.
    + eexists (cfgR2 _ _ _ _ _). split.
      1: apply RC1_Ov; lia.
      repeat split; try lia.
      2,3: solve_pow2_lt.
      rewrite Nat.mul_add_distr_r in HP.
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbitS_cases m.
    eexists (cfgR1 _ _ _ _ _). split.
    1: apply RC2_Ov; lia.
    repeat split; try lia.
    2,3: solve_pow2_lt.
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

End V8.
End V8.


Module TM172.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RE0RA_1RF---_1RA1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ C A [1;1] [0;1] 7 59 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM172.

Module TM173.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LF_1LD1RF_1LE0LD_1RC1LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ E C [1;1] [0;1] 6 18 4).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM173.

Module TM175.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LF_1LD1RF_0LE0LD_1RE0RC_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ E C [0;1] [0;1] 10 555 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM175.

Module TM176.
Definition tm := Eval compute in (TM_from_str "1RB1LE_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ D B [0;1] [0;1] 6 19 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM176.

Module TM177.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LA_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ F D [0;1] [0;1] 9 267 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM177.

Module TM178.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1LD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ C A [0;1] [0;1] 7 59 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM178.

Module TM180.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD1LF_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ F D [0;1] [0;1] 9 267 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM180.

Module TM181.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LE_1LD1RF_0LE0LD_1RE0RC_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ E C [0;1] [0;1] 10 555 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM181.

Module TM182.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ D B [0;1] [0;1] 6 19 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM182.

Module TM183.
Definition tm := Eval compute in (TM_from_str "1LB1RD_0LC0LB_1RC0RA_1RE0RA_1RF---_1RA1LC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V8.nonhalt _ C A [0;1] [0;1] 7 59 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM183.

Module V9.
Section V9.
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
  l <| rd0^^(n+1) *> [0;0;0] *> r.

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
  LC lenL k <| RC2 (i+lenR+1) (((2^(i+lenR)-1)*2+1)*2+1) m.
Proof.
  replace (2^(i+lenR)) with ((2^i-1+1)*2^lenR) by (rewrite Nat.pow_add_r; f_equal; lia).
  solve_rule ROv2.
Qed.

Lemma RC2_Ov_0 lenL lenR k:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 0 -->+
  LC lenL k <| RC 0.
Proof.
  intros.
  unfold LC,RC,RC2.
  rw_Bin.
  follow10 ROv2.
  cbn.
  repeat rewrite <-const_unfold.
  rewrite lpow_all0.
  2: solve_const0_eq.
  finish.
Qed.

Lemma LC_Ov lenL n i:
  LC lenL O <| RC ((n*2+1)*2^i) -->+
  LC lenL (2^lenL-1) |> RC1 i ((2^i-1)*2) n.
Proof.
  solve_rule LOv.
Qed.

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

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
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgR lenL k n => k<2^lenL /\ 2 <= k+n+1 < 2^lenL
| cfgR1 lenL k lenR n m => n+m <= k < 2^lenL /\ n<2^(lenR+1) /\
  (lenR=O -> n=O -> m=O -> k+1 <> 2^lenL)
| cfgR2 lenL k lenR n m => n+m*2^lenR*4+2 <= k < 2^lenL /\ n<2^(lenR+1)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

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
      pose proof (split_bound_v1 x i lenL).
      lia'.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR1 _ _ _ _ _). split.
      1: follow10 RC1_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbit_cases m.
    + eexists (cfgR _ _ _). split.
      1: apply RC1_Ov_0; lia.
      destruct lenR. 1: lia'.
      replace (S lenR*2) with (lenR*2+2) by lia.
      pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(lenR*2))).
      lia'.
    + eexists (cfgR2 _ _ _ _ _). split.
      1: apply RC1_Ov; lia.
      repeat split; try lia.
      2,3: solve_pow2_lt.
      pose proof (split_bound_v2 x i).
      zify_le_mul_r; lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbit_cases m.
    + eexists (cfgL _ _ _). split.
      1: apply RC2_Ov_0; lia.
      lia'.
    + destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Ov; follow100 LC_Inc; finish.
      lia'.
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

End V9.
End V9.

Module TM17.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1RE_1RF0RA_0LB0LD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V9.nonhalt _ C A [1;1] [0;1] 4 9 2).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM17.

Module TM57.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0LE_1LE1RA_0LF0LE_1RF0RD").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V9.nonhalt _ F D [0;1] [0;1] 3 3 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM57.

Module TM58.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC1RE_0LD0LC_1RD0RB_1RF0RB_1RA---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V9.nonhalt _ D B [0;1] [0;1] 2 1 1).
  1-5: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM58.

Module V7c.
Section V7c.
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
  ldh <* ld1^^(n+1) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> rd0^^m *> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0;0] *> r.

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
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC lenL k <| RC2 (i0+1+(lenR+i+1)) ((((2^i0-1)*2+1)*2^(lenR+i+1)-1)*2+1) m.
Proof.
  solve_rule ROv2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC lenL k <| RC (2^(lenR+i+2)).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i i0:
  LC (lenL+1) O <| RC (((n*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2+1) |> RC2 (i0+i) (((2^i0-1)*2+1)*2^i-1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  LC (lenL+1) O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2+1) |> RC (2^i).
Proof.
  solve_rule LOv.
Qed.

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

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
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR2 lenL k lenR n m => lenL>=1 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4+1 < n+2^lenL*2)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct lenL. 1: lia.
      cbn[Nat.pow] in *.
      lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: replace (S lenL) with (lenL+1) by lia; apply LC_Ov_0.
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: replace (S lenL) with (lenL+1) by lia; apply LC_Ov.
        repeat split; try lia'.
        1: replace (i0+i+1) with (i0+1+i) by lia; solve_pow2_lt.
        intro; subst.
        pp_pow2_lt_le (i0+i+1) (lenL+2).
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbitS_cases m.
    lowbit_cases x.
    * eexists (cfgL _ _ _). split.
      1: apply RC2_Ov_0; lia.
      repeat split; try lia'.
      destruct i.
      1: lia'.
      pp_pow2_lt_le (i+lenR+2) lenL.
      cbn[Nat.pow] in *.
      pose proof (Nat.mul_le_mono_pos_r (2^i) (2^i*2-1) (2^lenR)).
      lia.
    * destruct k.
      1: zify_pow2sub1; lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Ov; follow100 LC_Inc; finish.
      repeat split; try lia.
      2: solve_pow2_lt.
      -- repeat rewrite Nat.pow_add_r in *.
         zify_pow2sub1; lia.
      -- intro; subst.
         pp_pow2_lt_le (i0+i+lenR+3) lenL.
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

End V7c.
End V7c.


Module V7d.
Section V7d.
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
  ldh <* ld1^^(n+1) <| rd1^^m *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld1 |> rd0^^m *> [1;0;0] *> r.

Hypothesis ROv2:
  forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(n+m+2) *> [1;0;0] *> r.

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
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 (((m*2+1)*2^i0*2+1)*2^i-1) -->+
  LC lenL k <| RC2 (i0+1+(lenR+i+1)) ((((2^i0-1)*2+1)*2^(lenR+i+1)-1)*2+1) m.
Proof.
  solve_rule ROv2.
  simpl_rotate.
  reflexivity.
Qed.

Lemma RC2_Ov_0 lenL lenR k i:
  k<2^lenL ->
  LC lenL k |> RC2 lenR 0 ((0*2+1)*2^i-1) -->+
  LC lenL k <| RC (2^(lenR+i+2)).
Proof.
  solve_rule ROv2.
Qed.

Lemma LC_Ov lenL n i i0:
  LC (lenL+1) O <| RC (((n*2+1)*2^i0*2+1)*2^i-1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2) |> RC2 (i0+i) (((2^i0-1)*2+1)*2^i-1) n.
Proof.
  solve_rule LOv.
Qed.

Lemma LC_Ov_0 lenL i:
  LC (lenL+1) O <| RC ((0*2+1)*2^i-1) -->+
  LC (lenL+1+1) ((2^lenL-1)*2*2) |> RC (2^i).
Proof.
  solve_rule LOv.
Qed.

Ltac follow10 H :=
  eapply progress_evstep_trans; [apply H; try lia | ].

Ltac follow100 H :=
  eapply progress_evstep; follow10 H.

Ltac lia' :=
  repeat rewrite Nat.pow_add_r; lia.

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
| cfgL lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n < 2^lenL*2
| cfgR lenL k n => lenL>=1 /\ k<2^lenL /\ 2 <= k+n+1 < 2^lenL*2
| cfgR2 lenL k lenR n m => lenL>=1 /\ n+m*2^lenR*4 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (m=O -> k+2^lenR*4+1 < n+2^lenL*2)
end.

Ltac pp_pow2_lt_le x y :=
  pose proof (Nat.pow_lt_mono_r_iff 2 x y);
  pose proof (Nat.pow_le_mono_r_iff 2 (x+1) y);
  repeat rewrite Nat.pow_add_r in *.

Lemma closed x:
  P x ->
  exists x', to_config x -->+ to_config x' /\ P x'.
Proof.
  unfold P,to_config.
  intros HP.
  destruct x.
  - destruct k as [|k].
    + destruct lenL. 1: lia.
      cbn[Nat.pow] in *.
      lowbitS_cases n.
      lowbit_cases x.
      * eexists (cfgR _ _ _). split.
        1: replace (S lenL) with (lenL+1) by lia; apply LC_Ov_0.
        lia'.
      * eexists (cfgR2 _ _ _ _ _). split.
        1: replace (S lenL) with (lenL+1) by lia; apply LC_Ov.
        repeat split; try lia'.
        1: replace (i0+i+1) with (i0+1+i) by lia; solve_pow2_lt.
        intro; subst.
        pp_pow2_lt_le (i0+i+1) (lenL+2).
        lia.
    + eexists (cfgR _ _ _). split.
      1: apply LC_Inc; lia.
      lia.
  - eexists (cfgL _ _ _). split.
    apply RC_Inc.
    lia.
  - destruct n as [|n].
    2: {
      destruct k. 1: lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Inc; follow100 LC_Inc; finish.
      lia.
    }
    lowbitS_cases m.
    lowbit_cases x.
    * eexists (cfgL _ _ _). split.
      1: apply RC2_Ov_0; lia.
      repeat split; try lia'.
      destruct i.
      1: lia'.
      pp_pow2_lt_le (i+lenR+2) lenL.
      cbn[Nat.pow] in *.
      pose proof (Nat.mul_le_mono_pos_r (2^i) (2^i*2-1) (2^lenR)).
      lia.
    * destruct k.
      1: zify_pow2sub1; lia.
      eexists (cfgR2 _ _ _ _ _). split.
      1: follow10 RC2_Ov; follow100 LC_Inc; finish.
      repeat split; try lia.
      2: solve_pow2_lt.
      -- repeat rewrite Nat.pow_add_r in *.
         zify_pow2sub1; lia.
      -- intro; subst.
         pp_pow2_lt_le (i0+i+lenR+3) lenL.
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

End V7d.
End V7d.

Module TM238.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RE_1LD1RF_1RE0LD_1LB1LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7d.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 1).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM238.

Module TM239.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1LB_1RD0RB_1LA1RE_1RF0RD_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7d.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 3 0 10).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM239.

Module TM240.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC0RA_1LF1RD_1RE0RC_1RB---_1RA0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7d.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 3 0 11).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM240.

Module TM241.
Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LE_1RA0RB_1RF0RA_0RA0LE_1RC---").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7c.nonhalt _ C A [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 3).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM241.

Module TM242.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0RD_1LD1RF_1LB0LE_0RC0LE_1RA0RC").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7c.nonhalt _ B C [1;1;1;0;0;0] [1;1;1;1;0;1] 2 1 4).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM242.

Module TM243.
Definition tm := Eval compute in (TM_from_str "1RB0RD_1RC---_1RD0RE_1LE1RA_1LC0LF_0RD0LF").
Lemma nonhalt: ~halts tm c0.
Proof.
  eapply (V7c.nonhalt _ C D [1;1;1;0;0;0] [1;1;1;1;0;1] 3 6 2).
  1-4: es.
  1: esx.
  1: cbn; lia.
Qed.
End TM243.

