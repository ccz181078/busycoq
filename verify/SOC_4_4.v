From BusyCoq Require Import Individual62 BinaryCounter_v2.
From BusyCoq Require Import ES_v2.
Require Import ZifyNat.
Require Import Lia PeanoNat String.

Notation ld0 := <[1;1;1;0].
Notation ld1 := <[1;1;1;1].
Notation ldh := (const 0 <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].


Definition LC len n := BinDec ld0 ld1 len n ldh.
Definition RC n := BinInc rd1 n.
Definition RC1 len n m := BinDec2 [0] [1] [0;0;0] len n (rd1 *> BinInc rd1 m). 

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

Ltac solve_v1 k lenL x :=
  pose proof (Nat.mul_le_mono_pos_r (k+1) (2^lenL) (2^(x)));
  rw_pa;
  spl;
  zify_le_mul_r; lia.

Ltac eex f :=
  (eexists (f _ _ _ _ _) ||
  eexists (f _ _ _ _) ||
  eexists (f _ _ _)); split.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RD_0RD1RF_1LE0LA_0LB---_1LD0RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{B}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1;1] {{F}}> r) (at level 30).

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

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n |> [1] *> r.
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

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC1 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC 1.
Proof.
  epose proof (ROv _ 0inf _) as I1.
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
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=O -> m=O -> k+1<2^lenL)
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
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      rw_pa.
      destruct lenR.
      1: lia.
      cbn[Nat.pow] in *.
      solve_v1 k lenL lenR.
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      epose proof (split_bound_v2 x i).
      spl.
      * destruct lenR.
        1: lia.
        solve_v1 k lenL lenR.
      * intros.
        subst.
        solve_v1 k lenL lenR.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 5 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM1.


Module TM3.
Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC0LF_0LD---_1RE0RB_0RB1RA_1RD0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{D}} [0;1;1;1;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;0;1;1;1] {{A}}> r) (at level 30).

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

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n |> [1] *> r.
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

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC1 i ((2^i-1)*2) x.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC 1.
Proof.
  epose proof (ROv _ 0inf _) as I1.
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
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=O -> m=O -> k+1<2^lenL)
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
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      rw_pa.
      destruct lenR.
      1: lia.
      cbn[Nat.pow] in *.
      solve_v1 k lenL lenR.
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      epose proof (split_bound_v2 x i).
      spl.
      * destruct lenR.
        1: lia.
        solve_v1 k lenL lenR.
      * intros.
        subst.
        solve_v1 k lenL lenR.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 5 11 1)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM3.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RE_0LC0LB_1RC0RD_1RA0LE_1RF0RD_1RD---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} [0;0;1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{A}}> r) (at level 30).

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

Lemma ROv l r n:
  l |> rd1^^n *> [1] *> rd1 *> r -->+
  l <* ld1 <* ld0^^n |> [0] *> r.
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

Lemma RC1_Ov lenL k lenR x i:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 ((x*2+1)*2^i) -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC1 i ((2^i-1)*2+1) x.
Proof.
  solve_rule ROv.
Qed.

Lemma RC1_Ov_0 lenL k lenR:
  k<2^lenL ->
  LC lenL k |> RC1 lenR 0 0 -->+
  LC (lenL+1+lenR) ((k*2+1)*2^lenR-1) |> RC 0.
Proof.
  epose proof (ROv _ 0inf _) as I1.
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
| cfgL lenL k n => k<2^lenL /\ 2 <= k+n < 2^lenL
| cfgR1 lenL k lenR n m => n+m+1 <= k < 2^lenL /\ n<2^(lenR+1) /\
    (lenR=O -> n=O -> m=O -> k+1<2^lenL)
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
    lowbit_cases m.
    + eex cfgL.
      1: follow10 RC1_Ov_0; follow100 RC_Inc; finish.
      spl.
      rw_pa.
      destruct lenR.
      1: lia.
      cbn[Nat.pow] in *.
      solve_v1 k lenL lenR.
    + eex cfgR1.
      1: apply RC1_Ov; lia.
      epose proof (split_bound_v2 x i).
      spl.
      destruct lenR.
      1: lia.
      solve_v1 k lenL lenR.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config (cfgL 4 9 2)).
  1: esx.
  eapply progress_nonhalt_cond.
  1: apply closed.
  cbn; lia.
Qed.

End TM2.



