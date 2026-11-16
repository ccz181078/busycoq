(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import String ZifyNat Lia PeanoNat NArith.

(* SOC34_Ex2.TM2 *)
Module TM1.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import String ZifyNat Lia PeanoNat NArith.


Lemma lpow_unrotate_12 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.

Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA1LC_1RF1RE_0LC0RA_1RC---").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{C}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1;0] {{A}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n: ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma R110 l r n:
  l <* ld0 <* ld1^^n |> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^n |> [1;1;0] *> r.
Proof. es. Qed.
Lemma R111 l r: l |> [1;1;1] *> r -->+ l <* ld0 |> r.
Proof. es. Qed.
Lemma ROv110 r n:
  ldh <* ld1^^n |> [1;1;0] *> r -->+ ldh <* ld0^^(n+1) |> [0] *> r.
Proof. es. Qed.
Lemma R110_prepare l r n:
  l |> rd1^^n *> [1;1;0] *> r -->+
  l <* ld1 {{A}}> [1]^^(n*4+2) *> [0] *> r.
Proof. es' n & l r. Qed.
Lemma R1001_prepare l r n:
  l |> rd1^^n *> [1;0;0;1] *> r -->+
  l <* ld1 {{A}}> [1]^^(n*4+4) *> r.
Proof. es' n & l r. Qed.
Lemma A_ones l r n:
  l {{A}}> [1]^^(n*3) *> r -[tm]->* l <* ld0^^n {{A}}> r.
Proof. es' n & l r. Qed.
Ltac finish12 := st; simpl_tape; try flia;
  repeat rewrite <-lpow_unrotate_12; reflexivity.
Lemma ROv110_0 l r n:
  l |> rd1^^(n*3+3) *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(n*4+3) |> [1;1;0] *> r.
Proof.
  eapply progress_evstep_trans; [apply R110_prepare|].
  applys_eq (A_ones (l <* ld1) ([1;1;0] *> r) (n*4+4)); finish12.
Qed.
Lemma ROv110_1 l r n:
  l |> rd1^^(n*3+1) *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(n*4+1) |> [0] *> r.
Proof.
  eapply progress_evstep_trans; [apply R110_prepare|].
  applys_eq (A_ones (l <* ld1) ([0] *> r) (n*4+2)); finish12.
Qed.
Lemma ROv110_2 l r n:
  l |> rd1^^(n*3+2) *> [1;1;0] *> r -->+
  l <* ld1 <* ld0^^(n*4+2) |> [1;0] *> r.
Proof.
  eapply progress_evstep_trans; [apply R110_prepare|].
  applys_eq (A_ones (l <* ld1) ([1;0] *> r) (n*4+3)); finish12.
Qed.
Lemma ROv1001_0 l r n:
  l |> rd1^^(n*3) *> [1;0;0;1] *> r -->+
  l <* ld1 <* ld0^^(n*4) |> [1] *> r.
Proof.
  eapply progress_evstep_trans; [apply R1001_prepare|].
  applys_eq (A_ones (l <* ld1) ([1] *> r) (n*4+1)); finish12.
Qed.
Lemma ROv1001_1 l r n:
  l |> rd1^^(n*3+1) *> [1;0;0;1] *> r -->+
  l <* ld1 <* ld0^^(n*4+1) |> [1;1] *> r.
Proof.
  eapply progress_evstep_trans; [apply R1001_prepare|].
  applys_eq (A_ones (l <* ld1) ([1;1] *> r) (n*4+2)); finish12.
Qed.
Lemma ROv1001_2 l r n:
  l |> rd1^^(n*3+2) *> [1;0;0;1] *> r -->+
  l <* ld1 <* ld0^^(n*4+3) |> r.
Proof.
  eapply progress_evstep_trans; [apply R1001_prepare|].
  applys_eq (A_ones (l <* ld1) r (n*4+4)); finish12.
Qed.
Lemma init: c0 -[tm]->* ldh <* ld1 <| rd0 *> rd1 *> 0inf.
Proof. esx. Qed.

Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0;0] h n r.

Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
  solve [lia|nia|flia].
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,MC; rw_Bin;
  try solve [arith]; follow_rule H.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_split len k: 1+k<2^len -> exists l n,
  LC len (1+k)=l <* ld0 <* ld1^^n /\ LC len k=l <* ld1 <* ld0^^n.
Proof.
  unfold LC,BinDec; intros HK.
  assert (HE: Pos.of_nat (2^(len+1)-1-k)=Pos.succ (Pos.of_nat (2^(len+1)-1-(1+k)))) by arith.
  rewrite HE; eapply not_full_Inc; rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len); [rewrite pow2'_spec'; arith|arith].
Qed.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc l m: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc l h n r: 1+n<2^(h+1) -> l |> MC h (1+n) r -->+ l <| MC h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma MC_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> MC h n r -->* LC len k |> MC h 0 r.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc MC_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma MC_partial len k h n r: k<2^len -> k+1<=n<2^(h+1) ->
  LC len k |> MC h n r -->+ LC len 0 <| MC h (n-(k+1)) r.
Proof.
  gen n; induction k; intros n HK HN.
  - applys_eq (MC_Inc (LC len 0) h (n-1) r); [flia|lia].
  - eapply progress_evstep_trans; [applys_eq (MC_Inc (LC len (S k)) h (n-1) r); [flia|lia]|].
    follow_inc LC_Inc.
    apply progress_evstep; applys_eq (IHk (n-1)); [flia|lia|lia].
Qed.
Lemma MC_Incs_pos len k h n r: 1<=n -> k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> MC h n r -->+ LC len k |> MC h 0 r.
Proof.
  destruct n; intros; [lia|].
  eapply progress_evstep_trans; [apply MC_Inc; lia|].
  rewrite Nat.add_succ_r; follow_inc LC_Inc; apply MC_Incs; lia.
Qed.
Lemma RC_Incs len k m: k<2^len ->
  LC len k |> RC m -->+ LC len 0 <| RC (m+k+1).
Proof.
  gen m; induction k; intros m HK.
  - applys_eq RC_Inc; flia.
  - follow10 RC_Inc; follow_inc LC_Inc.
    apply progress_evstep; applys_eq IHk; [flia|lia].
Qed.
Lemma LC_Ov len r:
  LC len 0 <| r -->+ LC len (2^len-1) |> [1] *> r.
Proof. solve_rule LOv. Qed.
Lemma LC_R110_dec len k r: 1+k<2^len ->
  LC len (1+k) |> [1;1;0] *> r -->+ LC len k |> [1;1;0] *> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  rewrite HA,HB; apply R110.
Qed.
Lemma LC_R110 len k r: k<2^len ->
  LC len k |> [1;1;0] *> r -->+ LC (len+1) (2^(len+1)-1) |> [0] *> r.
Proof.
  induction k; intros HK.
  - solve_rule ROv110.
  - eapply progress_evstep_trans; [apply LC_R110_dec; lia|].
    apply progress_evstep; apply IHk; lia.
Qed.

Lemma R110_0 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3) *> [1;1;0] *> r -->+
  LC (len+a*4+1) (2^(len+a*4+1)-1) |> [0] *> r.
Proof.
  intros HK; destruct a as [|a].
  - cbn [Nat.mul lpow]; applys_eq LC_R110; [flia|lia].
  - eapply progress_evstep_trans.
    + applys_eq (ROv110_0 (LC len k) r a); flia.
    + apply progress_evstep.
      applys_eq (LC_R110 (len+1+(a*4+3)) ((k*2+1)*2^(a*4+3)-1) r).
      * unfold LC; rw_Bin; try solve [arith]; flia.
      * flia.
      * arith.
Qed.
Lemma R110_1 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3+1) *> [1;1;0] *> r -->+
  LC (len+1+(a*4+1)) ((k*2+1)*2^(a*4+1)-1) |> [0] *> r.
Proof. solve_rule ROv110_1. Qed.
Lemma R110_2 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3+2) *> [1;1;0] *> r -->+
  LC (len+1+(a*4+2)) ((k*2+1)*2^(a*4+2)-1) |> [1;0] *> r.
Proof. solve_rule ROv110_2. Qed.
Lemma R1001_0 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3) *> [1;0;0;1] *> r -->+
  LC (len+1+a*4) ((k*2+1)*2^(a*4)-1) |> [1] *> r.
Proof. solve_rule ROv1001_0. Qed.
Lemma R1001_1 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3+1) *> [1;0;0;1] *> r -->+
  LC (len+1+(a*4+1)) ((k*2+1)*2^(a*4+1)-1) |> [1;1] *> r.
Proof. solve_rule ROv1001_1. Qed.
Lemma R1001_2 len k a r: k<2^len ->
  LC len k |> rd1^^(a*3+2) *> [1;0;0;1] *> r -->+
  LC (len+1+(a*4+3)) ((k*2+1)*2^(a*4+3)-1) |> r.
Proof. solve_rule ROv1001_2. Qed.
Lemma LC_R111 len k r: k<2^len ->
  LC len k |> [1;1;1] *> r -->+ LC (len+1) (k*2+1) |> r.
Proof. solve_rule R111. Qed.

Lemma R1_shape h m:
  [1] *> RC ((m*2+1)*2^h) = MC h ((2^h-1)*2) (rd1 *> RC m).
Proof.
  unfold RC,MC; rw_Bin; cbv [BinaryCounter.d0 length List.repeat].
  simpl_rotate; st; reflexivity.
Qed.
Lemma R3_shape h m:
  [0;0;0] *> RC ((m*2+1)*2^h) = MC h (2^(h+1)-1) ([0;0] *> rd1 *> RC m).
Proof.
  unfold RC,MC; rw_Bin; cbv [BinaryCounter.d0 length List.repeat].
  simpl_rotate; st; reflexivity.
Qed.
Lemma edge_shape n:
  MC (n+1) ((2^n-1)*2) (rd1 *> 0inf) = rd1 *> rd0^^n *> [1;1] *> 0inf.
Proof.
  unfold MC; rewrite BinDec2_mul2.
  replace (n+1) with (0+1+n) by lia.
  replace (2^n-1) with ((0*2+1)*2^n-1) by lia.
  rewrite BinDec_mulpow2sub1 by arith.
  rw_Bin; st; simpl_rotate; reflexivity.
Qed.

Lemma F_start len h m k: k+(2^h-1)*2=2^len-1 ->
  LC len 0 <| RC ((m*2+1)*2^h) -->+
  LC len k |> rd1^^h *> [1;1;0;0;0] *> RC m.
Proof.
  intros HK; eapply progress_evstep_trans; [apply LC_Ov|].
  rewrite R1_shape,<-HK; eapply evstep_trans; [apply MC_Incs; arith|].
  unfold MC; rw_Bin; st; finish.
Qed.
Lemma Z_start len k h m: k+(2^(h+1)-1)<2^len ->
  LC len (k+(2^(h+1)-1)) |> [0;0;0] *> RC ((m*2+1)*2^h) -->+
  LC len k |> rd1^^h *> [1;0;0;1;0;0;0] *> RC m.
Proof.
  intros HK; rewrite R3_shape; eapply progress_evstep_trans; [apply MC_Incs_pos; arith|].
  unfold MC; rw_Bin; st; finish.
Qed.
Lemma F_edge n:
  LC (n+1) 0 <| RC (2^(n+1)) -->+
  LC (n+1) 0 <| rd1 *> rd0^^n *> [1;1] *> 0inf.
Proof.
  eapply progress_evstep_trans; [apply LC_Ov|].
  apply progress_evstep.
  applys_eq (MC_partial (n+1) (2^(n+1)-1) (n+1) ((2^(n+1)-1)*2) (rd1 *> 0inf)).
  - unfold RC,MC; rw_Bin; cbv [BinaryCounter.d0 length List.repeat]; st; reflexivity.
  - rewrite <-edge_shape.
    replace ((2^(n+1)-1)*2-(2^(n+1)-1+1)) with ((2^n-1)*2) by arith.
    reflexivity.
  - arith.
  - arith.
Qed.

Lemma E_prepare n:
  LC (n+1) 0 <| rd1 *> rd0^^n *> [1;1] *> 0inf -->+
  LC (n+2) (2^(n+1)) |> rd1^^n *> [1;0;0;1;1] *> 0inf.
Proof.
  eapply progress_evstep_trans; [apply LC_Ov|].
  eapply evstep_trans.
  - apply progress_evstep; applys_eq (LC_R110 (n+1) (2^(n+1)-1) ([0;0] *> rd0^^n *> [1;1] *> 0inf));
      try (st; reflexivity); arith.
  - applys_eq (MC_Incs (n+2) (2^(n+1)) n (2^(n+1)-1) ([0;0;1;1] *> 0inf)).
    + replace (2^(n+1)+(2^(n+1)-1)) with (2^(n+2)-1) by arith.
      unfold MC; rw_Bin; st; simpl_rotate; flia.
    + unfold MC; rw_Bin; st; reflexivity.
    + arith.
    + arith.
Qed.

Inductive Config :=
| cfgF (len m:nat)
| cfgA (len k h m:nat)
| cfgB (len k h m:nat)
| cfgZ (len k m:nat)
| cfgN (len k m:nat)
| cfgE (n:nat).
Definition to_config x := match x with
| cfgF len m => LC len 0 <| RC m
| cfgA len k h m => LC len k |> rd1^^h *> [1;1;0;0;0] *> RC m
| cfgB len k h m => LC len k |> rd1^^h *> [1;0;0;1;0;0;0] *> RC m
| cfgZ len k m => LC len k |> [0;0;0] *> RC m
| cfgN len k m => LC len k |> RC m
| cfgE n => LC (n+1) 0 <| rd1 *> rd0^^n *> [1;1] *> 0inf
end.
Close Scope sym.
Definition P x := match x with
| cfgF len m => 1<=len /\ 0<m<2^(len+1)
| cfgA len k h m => k<2^len /\ k+2^(h+1)-1<=2^len /\ (m+1)*2^h<=k+2^(h+1)-1
| cfgB len k h m => k<2^len /\ k+2^(h+1)-1<=2^len /\ (m+1)*2^(h+1)<=k+2^(h+1)-1
| cfgZ len k m => 1<=len /\ k<2^len /\ m*2<=k
| cfgN len k m => 1<=len /\ k<2^len /\ m+k+1<2^(len+1)
| cfgE _ => True
end.

Lemma mod3_cases h: exists a, h=a*3 \/ h=a*3+1 \/ h=a*3+2.
Proof.
  exists (h/3); pose proof (Nat.div_mod h 3 ltac:(lia));
  pose proof (Nat.mod_upper_bound h 3 ltac:(lia)); lia.
Qed.
Lemma F_budget len h m: (m*2+1)*2^h<2^(len+1) ->
  h<=len /\ (m+1)*2^h<=2^len.
Proof.
  intros HM; assert (HH: h<=len).
  { assert (2^h<2^(len+1)) by nia; apply Nat.pow_lt_mono_r_iff in H; lia. }
  split; [lia|].
  assert (HM': m*2+1<2^(len-h+1)).
  { apply (proj2 (Nat.mul_lt_mono_pos_r (2^h) _ _ ltac:(lia))).
    rewrite <-Nat.pow_add_r; applys_eq HM; flia. }
  replace len with ((len-h)+h) by lia; rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r; rewrite pow2_S in HM'; lia.
Qed.
Open Scope sym.

Ltac counter_rule H := cbn [to_config]; applys_eq H;
  try solve [unfold RC; rw_Bin; st; reflexivity | lia].

Lemma A_closed len k h m: P (cfgA len k h m) ->
  exists y, to_config (cfgA len k h m) -->+ to_config y /\ P y.
Proof.
  intros [HK [HC HM]]; destruct (mod3_cases h) as [a [-> | [-> | ->]]].
  - exists (cfgZ (len+a*4+1) (2^(len+a*4+1)-1) m); split.
    + counter_rule R110_0.
    + cbn [P]; repeat split; arith.
  - exists (cfgZ (len+1+(a*4+1)) ((k*2+1)*2^(a*4+1)-1) m); split.
    + counter_rule R110_1.
    + cbn [P]; repeat split; arith.
  - exists (cfgN (len+1+(a*4+2)) ((k*2+1)*2^(a*4+2)-1) (m*2+1)); split.
    + counter_rule R110_2.
    + cbn [P]; repeat split; arith.
Qed.
Lemma B_closed len k h m: P (cfgB len k h m) ->
  exists y, to_config (cfgB len k h m) -->+ to_config y /\ P y.
Proof.
  intros [HK [HC HM]]; destruct (mod3_cases h) as [a [-> | [-> | ->]]].
  - exists (cfgN (len+1+a*4) ((k*2+1)*2^(a*4)-1) (m*2+1)); split.
    + counter_rule R1001_0.
    + cbn [P]; repeat split; arith.
  - exists (cfgA (len+1+(a*4+1)) ((k*2+1)*2^(a*4+1)-1) 0 m); split.
    + counter_rule R1001_1.
    + cbn [P]; repeat split; arith.
  - exists (cfgZ (len+1+(a*4+3)) ((k*2+1)*2^(a*4+3)-1) m); split.
    + counter_rule R1001_2.
    + cbn [P]; repeat split; arith.
Qed.

Lemma F_closed len m: P (cfgF len m) ->
  exists y, to_config (cfgF len m) -->+ to_config y /\ P y.
Proof.
  intros [HL HM]; destruct (lowbit_cases' m) as [|m h]; [lia|].
  destruct (F_budget len h m ltac:(lia)) as [HH HB].
  destruct (Nat.eq_dec h len) as [->|HH'].
  - assert (m=0%nat) by nia; subst m; destruct len; [lia|].
    exists (cfgE len); split; [cbn [to_config]; applys_eq F_edge; flia|exact I].
  - assert (HC: 2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
    exists (cfgA len (2^len-1-(2^h-1)*2) h m); split.
    + cbn [to_config]; apply F_start; arith.
    + cbn [P]; repeat split; arith.
Qed.
Lemma Z_closed len k m: P (cfgZ len k m) ->
  exists y, to_config (cfgZ len k m) -->+ to_config y /\ P y.
Proof.
  intros [HL [HK HM]]; destruct (lowbit_cases' m) as [|m h].
  - exists (cfgF len (k+1)); split.
    + cbn [to_config]; applys_eq (RC_Incs len k 0);
        try solve [unfold RC; rw_Bin; st; reflexivity | flia].
    + cbn [P]; split; arith.
  - assert (HB: 2^(h+1)-1<=k) by arith.
    exists (cfgB len (k-(2^(h+1)-1)) h m); split.
    + cbn [to_config]; applys_eq Z_start; [flia|lia].
    + cbn [P]; repeat split; arith.
Qed.

Lemma E_closed n: exists y, to_config (cfgE n) -->+ to_config y /\ P y.
Proof.
  destruct (mod3_cases n) as [a [-> | [-> | ->]]].
  - exists (cfgN (a*3+2+1+a*4+1) (2^(a*3+2+1+a*4+1)-1) 0); split.
    + cbn [to_config]; eapply progress_evstep_trans; [apply E_prepare|].
      eapply evstep_trans.
      * apply progress_evstep; applys_eq (R1001_0 (a*3+2) (2^(a*3+1)) a ([1] *> 0inf));
          try (st; reflexivity); arith.
      * apply progress_evstep; counter_rule LC_R110; arith.
    + cbn [P]; repeat split; arith.
  - exists (cfgN (a*3+1+2+1+(a*4+1)+1)
      (((2^(a*3+1+1)*2+1)*2^(a*4+1)-1)*2+1) 0); split.
    + cbn [to_config]; eapply progress_evstep_trans; [apply E_prepare|].
      eapply evstep_trans.
      * apply progress_evstep; applys_eq (R1001_1 (a*3+1+2) (2^(a*3+1+1)) a ([1] *> 0inf));
          try (st; reflexivity); arith.
      * apply progress_evstep; counter_rule LC_R111; arith.
    + cbn [P]; repeat split; arith.
  - exists (cfgN (a*3+2+2+1+(a*4+3))
      ((2^(a*3+2+1)*2+1)*2^(a*4+3)-1) 1); split.
    + cbn [to_config]; eapply progress_evstep_trans; [apply E_prepare|].
      apply progress_evstep; counter_rule R1001_2; arith.
    + cbn [P]; repeat split; arith.
Qed.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x.
  - apply F_closed.
  - apply A_closed.
  - apply B_closed.
  - apply Z_closed.
  - intros [HL [HK HM]]; exists (cfgF len (m+k+1)); split.
    + cbn [to_config]; apply RC_Incs; lia.
    + cbn [P]; lia.
  - intros _; apply E_closed.
Qed.
Lemma init_counter: c0 -->* to_config (cfgF 1 2).
Proof. cbn [to_config]; unfold LC,RC; rw_Bin; apply init. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  eapply progress_nonhalt_cond with (P:=P); [apply closed|].
  cbn [P]; lia.
Qed.
End TM1.
