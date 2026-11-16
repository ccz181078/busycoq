(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat.
Require Import String.

(* Shared definitions from SOC43_Extra.v. *)
Module SOC43_Extra.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat.


Notation ld0 := <[1;1;1;0].
Notation ld1 := <[1;1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR QA:Q) (Erase:side->side->Prop).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{QR}}> r) (at level 30).
Notation "l |2> r" := (l <* ld0 {{QA}}> r) (at level 30).
Hypothesis Erase_O: Erase ldh ldh.
Hypothesis Erase_S0: forall l l', Erase l l' -> Erase (l<*ld0) (l'<*ld0).
Hypothesis Erase_S1: forall l l', Erase l l' -> Erase (l<*ld1) (l'<*ld0).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv_0: forall r n,
  ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n |> rd1 *> [0;0] *> r.
Hypothesis LOv_1: forall r n,
  ldh <* ld1^^n <| rd1 *> r -->+ ldh <* ld0^^(1+n) |> [0] *> r.
Hypothesis ROv1_0: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;0] *> r -->+ l' <* ld0^^(n*3+1) |> [0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*4+1) *> [1;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Hypothesis ROv1_2: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;0] *> r -->+ l' <* ld0^^(n*3+2) |> rd1 *> r.
Hypothesis ROv1_3: forall l r n,
  l |> rd1^^(n*4+3) *> [1;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n,
  l |> rd1^^(n*4) *> [1;0;1;0;0] *> r -->+ l <* ld0 <* ld1^^(n*3) |> [0] *> r.
Hypothesis ROv2_1: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+1) *> [1;0;1;0;0] *> r -->+ l' <* ld0^^(n*3+2) |> [1] *> r.
Hypothesis ROv2_2: forall l r n,
  l |> rd1^^(n*4+2) *> [1;0;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3+2) |2> r.
Hypothesis ROv2_3: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+3) *> [1;0;1;0;0] *> r -->+ l' <* ld0^^(n*3+4) |2> r.
Hypothesis Aux0: forall l r, l |2> rd0 *> r -->+ l |> [0;0] *> r.
Hypothesis Aux1: forall l r l', Erase l l' ->
  l |2> rd1 *> r -->+ l' <* ld0 |2> r.
Hypothesis Blank0: forall l l' n, Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;1] *> 0inf -->* l' <* ld0^^(n*3+1) |> rd1 *> 0inf.
Hypothesis Blank1: forall l n,
  l |> rd1^^(n*4+1) *> [1;1;0;1] *> 0inf -->* l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis Blank2: forall l l' n, Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;1] *> 0inf -->* l' <* ld0^^(n*3+3) |> 0inf.
Hypothesis Blank3: forall l n,
  l |> rd1^^(n*4+3) *> [1;1;0;1] *> 0inf -->* l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0] h n r.
Definition RC1 h n m := MC h n (rd1 *> RC m).
Definition RC2 h n m := MC h n ([0] *> rd1 *> RC m).
Definition RC' h n := MC h n ([1;0;1] *> 0inf).
Lemma RC_one_prefix: [1] *> RC 0 = RC 1.
Proof.
  unfold RC; rw_Bin; change ([1] *> 0inf = [1;0;0] *> 0inf).
  cbn; do 2 rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Lemma RC_zero_prefix: [0;0] *> RC 0 = RC 0.
Proof.
  unfold RC; rw_Bin; change ([0;0] *> 0inf = 0inf).
  cbn; do 2 rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first [follow10 HX|follow HX];
  repeat (simpl_rotate || simpl_tape); finish; repeat rewrite lpow_add'; flia.
Ltac solve_rule H := intros; unfold LC, RC1, RC2, RC', MC, RC in *;
  repeat rewrite BinDec_full in *;
  rw_Bin; try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Erase len k: k<2^len -> Erase (LC len k) (LC len (2^len-1)).
Proof.
  unfold LC; rewrite BinDec_full; gen k; induction len; intros.
  - replace k with 0%nat by (cbn in *; lia); rewrite BinDec_O; apply Erase_O.
  - replace (S len) with (len+1) in * by lia; divmod2_cases k;
      rw_Bin; try solve[arith]; simpl_tape;
      [apply Erase_S1|apply Erase_S0]; apply IHlen; arith.
Qed.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc m l: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc h n l r: 1+n<2^(h+1) -> l |> MC h (1+n) r -->+ l <| MC h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov_odd len m:
  LC len 0 <| RC (m*2+1) -->+ LC (len+1) (2^(len+1)-1) |> [0] *> RC m.
Proof. solve_rule LOv_1. Qed.
Lemma LC_Ov_zero len:
  LC len 0 <| RC 0 -->+ LC len (2^len-1) |> RC 1.
Proof. epose proof (LOv_0 0inf len) as H; solve_rule H. Qed.
Lemma LC_Ov_even len m i:
  LC len 0 <| RC ((m*2+1)*2^(i+1)) -->+
  LC len (2^len-1) |> RC2 (i+1) ((2^(i+1)-1)*2) m.
Proof. unfold LC,RC2,MC,RC; rw_Bin; try solve[arith]; simpl_tape; follow_rule LOv_0. Qed.

Lemma RC1_Ov0 len k a m: k<2^len ->
  LC len k |> RC1 (a*4) 0 m -->+
  LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> [0] *> RC m.
Proof. intros Hk; pose proof (ROv1_0 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC1_Ov1 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+1) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC (m*2+1).
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov2 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+2) 0 m -->+
  LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> RC (m*2+1).
Proof. intros Hk; pose proof (ROv1_2 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC1_Ov3 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+3) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0] *> RC m.
Proof. solve_rule ROv1_3. Qed.
Lemma RC2_Ov0 len k a m: k<2^len ->
  LC len k |> RC2 (a*4) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> [0] *> RC m.
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov1 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+1) 0 m -->+
  LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> [1] *> RC m.
Proof. intros Hk; pose proof (ROv2_1 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC2_Ov2 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+2) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |2> RC m.
Proof. solve_rule ROv2_2. Qed.
Lemma RC2_Ov3 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+3) 0 m -->+
  LC (len+(a*3+4)) (2^(len+(a*3+4))-1) |2> RC m.
Proof. intros Hk; pose proof (ROv2_3 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma Aux_even len k m:
  LC len k |2> RC (m*2) -->+ LC len k |> [0;0] *> RC m.
Proof. solve_rule Aux0. Qed.
Lemma Aux_odd len k m: k<2^len ->
  LC len k |2> RC (m*2+1) -->+ LC (len+1) (2^(len+1)-1) |2> RC m.
Proof. intros Hk; pose proof (Aux1 _ (RC m) _ (LC_Erase len k Hk)); solve_rule H. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma MC_finish len k h n r: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> MC h (n+k+1) r -->* LC len 0 <| MC h n r.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc MC_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc MC_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma MC_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> MC h n r -->* LC len k |> MC h 0 r.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc MC_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC2 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) (2^(len+1)-1) |> RC' h (2^(h+1)-1).
Proof.
  rewrite (Nat.add_comm h 1) at 1.
  unfold LC,RC2,RC',MC,RC; rw_Bin; try solve[arith].
  cbn [app lpow Str_app]; do 2 (rewrite (lpow_rotate [0;0] 0); cbn [app]); follow_rule LOv_1.
Qed.
Lemma corner_case h:
  LC (h+1) 0 <| RC (2^(h+1)) -->+
  LC (h+1+1) (2^(h+1)) |> RC' h 0.
Proof.
  replace (2^(h+1)) with ((0*2+1)*2^(h+1)) at 1 by arith.
  follow10 LC_Ov_even.
  replace ((2^(h+1)-1)*2) with
    (((0*2+1)*2^h-1)*2+(2^(h+1)-1)+1) by arith.
  unfold RC2; follow MC_finish; [arith|arith|].
  fold RC2; follow100 LC_Ov'.
  replace (2^(h+1+1)-1) with (2^(h+1)+(2^(h+1)-1)) by arith.
  unfold RC'; follow MC_Incs; [arith|arith|finish].
Qed.
Lemma RC'_Ov0 len k a: k<2^len ->
  LC len k |> RC' (a*4) 0 -->*
  LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> RC 1.
Proof. intros Hk; pose proof (Blank0 _ _ a (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC'_Ov1 len k a: k<2^len ->
  LC len k |> RC' (a*4+1) 0 -->*
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. solve_rule Blank1. Qed.
Lemma RC'_Ov2 len k a: k<2^len ->
  LC len k |> RC' (a*4+2) 0 -->*
  LC (len+(a*3+3)) (2^(len+(a*3+3))-1) |> RC 0.
Proof. intros Hk; pose proof (Blank2 _ _ a (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC'_Ov3 len k a: k<2^len ->
  LC len k |> RC' (a*4+3) 0 -->*
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. solve_rule Blank3. Qed.

Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat) | cfgA (len k m:nat).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgA len k m => LC len k |2> RC m
end.
Definition P x := match x with
| cfgL len k m => 1<=len /\ k<2^len /\ k+m<2^len*2
| cfgR len k m => 1<=len /\ k<2^len /\ k+m+1<2^len*2
| cfgR1 len k h n m | cfgR2 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgA len k m => 1<=len /\ m<=k<2^len
end.
Definition safe c := exists y, c=to_config y /\ P y.
Lemma safe_step c c': c -->+ c' -> safe c' ->
  exists y, c -->+ to_config y /\ P y.
Proof. intros H [y [E HP]]; subst c'; exists y; auto. Qed.
Lemma safe_Z0 len k m: 1<=len -> k<2^len -> m*2<=k+1 ->
  safe (LC len k |> [0]%sym *> RC m).
Proof.
  intros; assert (2<=2^len) by (destruct len; cbn in *; lia); lowbit_cases m.
  - exists (cfgR len k 0); split; [unfold to_config,RC; rw_Bin; reflexivity|cbn [P]; arith].
  - exists (cfgR1 len k i ((2^i-1)*2+1) x); split.
    + unfold to_config,RC1,MC,RC; rw_Bin; try solve[arith]; simpl_rotate; reflexivity.
    + cbn [P]; pose proof (split_bound_v2 x i); arith.
Qed.
Lemma safe_Z1 len k m: 1<=len -> k<2^len -> m*2<=k+2 ->
  safe (LC len k |> [1]%sym *> RC m).
Proof.
  intros; assert (2<=2^len) by (destruct len; cbn in *; lia); lowbit_cases m.
  - exists (cfgR len k 1); split.
    + unfold to_config; rewrite RC_one_prefix; reflexivity.
    + cbn [P]; arith.
  - exists (cfgR1 len k i ((2^i-1)*2) x); split.
    + unfold to_config,RC1,MC,RC; rw_Bin; try solve[arith]; simpl_rotate; reflexivity.
    + cbn [P]; pose proof (split_bound_v2 x i); arith.
Qed.
Lemma safe_Z00 len k m: 1<=len -> k<2^len -> m*2<=k+1 ->
  safe (LC len k |> [0;0]%sym *> RC m).
Proof.
  intros; assert (2<=2^len) by (destruct len; cbn in *; lia); lowbit_cases m.
  - exists (cfgR len k 0); split; [unfold to_config; rewrite RC_zero_prefix; reflexivity|cbn [P]; arith].
  - exists (cfgR2 len k i ((2^i-1)*2+1) x); split.
    + unfold to_config,RC2,MC,RC; rw_Bin; try solve[arith]; simpl_rotate; reflexivity.
    + cbn [P]; pose proof (split_bound_v2 x i); arith.
Qed.
Lemma append_bounds len k s: k<2^len ->
  k*2<=(k*2+1)*2^s-1<2^(len+1+s) /\
  (k*2+1)*2^s-1+k*2+2<2^(len+1+s)*2.
Proof. intros; arith. Qed.
Lemma divmod4 h: exists a, h=a*4 \/ h=a*4+1 \/ h=a*4+2 \/ h=a*4+3.
Proof.
  exists (h/4); pose proof (Nat.mod_upper_bound h 4 ltac:(lia));
  pose proof (Nat.div_mod h 4 ltac:(lia)); lia.
Qed.
Ltac divmod4_cases h := let a:=fresh "a" in
  destruct (divmod4 h) as [a [-> | [-> | [-> | ->]]]].

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len k m|len k m|len k h n m|len k h n m|len k m];
    cbn [P to_config]; intros HP;
    assert (2<=2^len) by (destruct len; cbn in *; lia).
  - destruct k as [|k].
    + destruct (Nat.eq_dec m (2^len)) as [E|E].
      * subst m; destruct len as [|h]; [cbn in HP; lia|].
        replace (S h) with (h+1) in * by lia; divmod4_cases h.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|apply RC'_Ov0; arith].
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|apply RC'_Ov1; arith].
           ++ cbn [P]; arith.
        -- eexists (cfgR _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|apply RC'_Ov2; arith].
           ++ cbn [P]; arith.
        -- eexists (cfgL _ _ _); split.
           ++ eapply progress_evstep_trans; [apply corner_case|apply RC'_Ov3; arith].
           ++ cbn [P]; arith.
      * divmod2_cases m.
        -- lowbit_cases n'.
           ++ eexists (cfgR _ _ _); split; [apply LC_Ov_zero|cbn [P]; arith].
           ++ replace ((x*2+1)*2^i*2) with ((x*2+1)*2^(i+1)) in * by arith.
              eexists (cfgR2 _ _ _ _ _); split; [apply LC_Ov_even|].
              cbn [P]; pose proof (split_bound_v3 x (i+1) len ltac:(lia) E); arith.
        -- eapply safe_step; [apply LC_Ov_odd|apply safe_Z0; arith].
    + eexists (cfgR _ _ _); split; [apply LC_Inc; lia|cbn [P]; lia].
  - eexists (cfgL _ _ _); split; [apply RC_Inc|cbn [P]; lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR1 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply MC_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod4_cases h.
    + eapply safe_step; [apply RC1_Ov0; lia|apply safe_Z0; arith].
    + eexists (cfgR _ _ _); split; [apply RC1_Ov1; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3) ltac:(lia)); lia.
    + eexists (cfgR _ _ _); split; [apply RC1_Ov2; lia|cbn [P]; arith].
    + eapply safe_step; [apply RC1_Ov3; lia|].
      pose proof (append_bounds len k (a*3+2) ltac:(lia)); apply safe_Z0; lia.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|].
      eexists (cfgR2 _ _ _ _ _); split.
      - eapply progress_evstep_trans; [apply MC_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - cbn [P]; lia. }
    divmod4_cases h.
    + eapply safe_step; [apply RC2_Ov0; lia|apply safe_Z0; arith].
    + eapply safe_step; [apply RC2_Ov1; lia|apply safe_Z1; arith].
    + eexists (cfgA _ _ _); split; [apply RC2_Ov2; lia|].
      cbn [P]; pose proof (append_bounds len k (a*3+2) ltac:(lia)); lia.
    + eexists (cfgA _ _ _); split; [apply RC2_Ov3; lia|cbn [P]; arith].
  - divmod2_cases m.
    + eapply safe_step; [apply Aux_even|apply safe_Z00; lia].
    + eexists (cfgA _ _ _); split; [apply Aux_odd; lia|cbn [P]; arith].
Qed.

Theorem nonhalt_from len k m:
  c0 -->* to_config (cfgL len k m) -> P (cfgL len k m) -> ~halts tm c0.
Proof.
  intros Hinit HP; eapply multistep_nonhalt; [exact Hinit|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|exact HP].
Qed.

End Counter.
End Counter.

Import String.

Open Scope sym.

Lemma lpow_unrotate_12 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::=
  rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 || rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_12.
End SOC43_Extra.

(* SOC43_Extra.TM10 *)
Module TM5.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat.

Import String.

Import SOC43_Extra.

Definition tm := Eval compute in (TM_from_str "1RB0RA_1LC1RE_1RD0LC_0LE0RF_1RA1LD_---1RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{B}}> r) (at level 30).
(* Canonical entry after the fixed prefix of the archive's LOv'. *)
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n |> rd1 *> [0;0] *> r.
Proof. es. Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*4+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv1_3 l r n:
  l |> rd1^^(n*4+3) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Definition LOv' l l' :=
  (forall r, l <* [1] <| r -->* l' |> [1;0] *> r).

Lemma ROv1_0 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+0) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+1) |> [0] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv1_2 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> rd1 *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv2_0 l r n:
  l |> rd1^^(n*4+0) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+1) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> [1] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Notation "l |2> r" := (l <* ld0 {{A}}> r) (at level 30).

Lemma ROv2_2 l r n:
  l |> rd1^^(n*4+2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |2> r.
Proof. st. repeat (er||sr). Qed.

Lemma ROv2_3 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+3) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+4) |2> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv'_1 l r l':
  LOv' l l' ->
  l |2> rd1 *> r -->+
  l' <* ld0 |2> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l |> [0;0] *> r.
Proof. es. Qed.


Definition Erase l l' := forall r, l <{{D}} [1;0;1;0;1;0] *> r -->* l' |> [1;0] *> r.
Lemma Erase_S0 l l': Erase l l' -> Erase (l<*ld0) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_S1 l l': Erase l l' -> Erase (l<*ld1) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_O: Erase ldh ldh.
Proof. unfold Erase; es. Qed.
Lemma Blank0 l l' n: Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+1) |> rd1 *> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank1 l n:
  l |> rd1^^(n*4+1) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. st; repeat (er || sr). Qed.
Lemma Blank2 l l' n: Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+3) |> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank3 l n:
  l |> rd1^^(n*4+3) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. st; repeat (er || sr). Qed.

Lemma Erase_LOv l l': Erase l l' ->
  forall r, l <* [1] <| r -->* l' |> [1;0] *> r.
Proof. unfold Erase; intros HP r; es; follow HP; es. Qed.
Lemma init: c0 -->* ldh <* ld1^^3 <| [1;0;0;0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=E) (QR:=B) (QA:=A)
    (Erase:=Erase) (len:=3) (k:=0%nat) (m:=9).
  all: try first [exact Erase_O|exact Erase_S0|exact Erase_S1|exact LInc|exact RInc|
    exact LOv_0|exact LOv_1|exact ROv1_1|exact ROv1_3|
    exact ROv2_2|exact ROv'_0|exact Blank0|exact Blank1|exact Blank2|exact Blank3|
    cbn [Counter.P]; lia|
    unfold Counter.to_config,Counter.LC,Counter.RC; rewrite BinDec_O; unfold BinInc; exact init].
  - intros l r n l' H; replace (n*4) with (n*4+0) by lia; apply ROv1_0; intro; apply Erase_LOv,H.
  - intros; apply ROv1_2; intro; apply Erase_LOv; assumption.
  - intros l r n; replace (n*4) with (n*4+0) by lia; apply ROv2_0.
  - intros; apply ROv2_1; intro; apply Erase_LOv; assumption.
  - intros; apply ROv2_3; intro; apply Erase_LOv; assumption.
  - intros; apply ROv'_1; intro; apply Erase_LOv; assumption.
Qed.
End TM5.

(* SOC43_Extra.TM12 *)
Module TM9.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat.

Import String.

Import SOC43_Extra.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_0LD0LD_1RE0RF_1RA0RE_0LB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{D}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{A}}> r) (at level 30).
(* Canonical entry after the fixed prefix of the archive's LOv'. *)
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n |> rd1 *> [0;0] *> r.
Proof. es. Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*4+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv1_3 l r n:
  l |> rd1^^(n*4+3) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Definition LOv' l l' :=
  (forall r, l <* [1] <| r -->* l' |> [1;0] *> r).

Lemma ROv1_0 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+0) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+1) |> [0] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv1_2 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> rd1 *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv2_0 l r n:
  l |> rd1^^(n*4+0) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+1) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> [1] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Notation "l |2> r" := (l <* ld0 {{E}}> r) (at level 30).

Lemma ROv2_2 l r n:
  l |> rd1^^(n*4+2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |2> r.
Proof. st. repeat (er||sr). Qed.

Lemma ROv2_3 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+3) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+4) |2> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv'_1 l r l':
  LOv' l l' ->
  l |2> rd1 *> r -->+
  l' <* ld0 |2> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l |> [0;0] *> r.
Proof. es. Qed.


Definition Erase l l' := forall r, l <{{C}} [1;0;1;0;1;0] *> r -->* l' |> [1;0] *> r.
Lemma Erase_S0 l l': Erase l l' -> Erase (l<*ld0) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_S1 l l': Erase l l' -> Erase (l<*ld1) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_O: Erase ldh ldh.
Proof. unfold Erase; es. Qed.
Lemma Blank0 l l' n: Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+1) |> rd1 *> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank1 l n:
  l |> rd1^^(n*4+1) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. st; repeat (er || sr). Qed.
Lemma Blank2 l l' n: Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+3) |> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank3 l n:
  l |> rd1^^(n*4+3) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. st; repeat (er || sr). Qed.

Lemma Erase_LOv l l': Erase l l' ->
  forall r, l <* [1] <| r -->* l' |> [1;0] *> r.
Proof. unfold Erase; intros HP r; es; follow HP; es. Qed.
Lemma init: c0 -->* ldh <* ld1^^3 <| [1;0;0;0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply Counter.nonhalt_from with (QL:=D) (QR:=A) (QA:=E)
    (Erase:=Erase) (len:=3) (k:=0%nat) (m:=9).
  all: try first [exact Erase_O|exact Erase_S0|exact Erase_S1|exact LInc|exact RInc|
    exact LOv_0|exact LOv_1|exact ROv1_1|exact ROv1_3|
    exact ROv2_2|exact ROv'_0|exact Blank0|exact Blank1|exact Blank2|exact Blank3|
    cbn [Counter.P]; lia|
    unfold Counter.to_config,Counter.LC,Counter.RC; rewrite BinDec_O; unfold BinInc; exact init].
  - intros l r n l' H; replace (n*4) with (n*4+0) by lia; apply ROv1_0; intro; apply Erase_LOv,H.
  - intros; apply ROv1_2; intro; apply Erase_LOv; assumption.
  - intros l r n; replace (n*4) with (n*4+0) by lia; apply ROv2_0.
  - intros; apply ROv2_1; intro; apply Erase_LOv; assumption.
  - intros; apply ROv2_3; intro; apply Erase_LOv; assumption.
  - intros; apply ROv'_1; intro; apply Erase_LOv; assumption.
Qed.
End TM9.
