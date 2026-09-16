(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Require Import ZifyNat Lia PeanoNat String.

(* SOC36_Ex3.TM3 *)
Module TM1.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1RB0RC_1RC1LB_1LD1RE_1LB0LD_0RF1RA_1RD---").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0;0].
Notation rd1 := [1;0;0;0;0;0].
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{B}} [1;1;1] *> r) (at level 30).
Notation "l |> r" := (l <* <[1;1;0] {{C}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(1+n) <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 |> rd0 *> [1] *> r.
Proof. es. Qed.
Lemma ROv1 l r n:
  l |> rd1^^n *> [1;1;0;0;0;0;0] *> r -->+
  l <| rd0^^n *> [0;0;0;0;1;0;0] *> r.
Proof. es. Qed.
Lemma ROv4 l r n:
  l |> rd1^^n *> [1;0;0;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*2+1) |> [0] *> r.
Proof. es. Qed.

(* Left remaining budget; right binary value; marked finite right counter. *)
Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0;0;0;0] h n r.

Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,MC; rw_Bin;
  try solve[solve_pow2_lt]; follow_rule H.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

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

Lemma MC_Ov1 l h m:
  l |> MC h 0 (rd1 *> RC m) -->+
  l <| MC h (2^(h+1)-1) ([0;0;0;1;0;0] *> RC m).
Proof. solve_rule ROv1. Qed.
Lemma MC_Ov4 len k h m: k<2^len ->
  LC len k |> MC h 0 ([0;0;0;1;0;0] *> RC m) -->+
  LC (len+1+(h*2+1)) ((k*2+1)*2^(h*2+1)-1) |> [0] *> RC m.
Proof. solve_rule ROv4. Qed.

Lemma Core len k h n m:
  k+n+1+(2^(h+1)-1)<2^len -> n<2^(h+1) ->
  LC len (k+n+1+(2^(h+1)-1)) |> MC h n (rd1 *> RC m) -->+
  LC (len+1+(h*2+1)) ((k*2+1)*2^(h*2+1)-1) |> [0] *> RC m.
Proof.
  intros HK HN.
  eapply evstep_progress_trans;
    [applys_eq (MC_Incs len (k+1+(2^(h+1)-1)) h n (rd1 *> RC m)); [flia|lia|lia]|].
  follow10 MC_Ov1.
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_Inc len (k+(2^(h+1)-1))); [flia|lia]|].
  eapply evstep_trans; [apply MC_Incs; lia|].
  apply progress_evstep; apply MC_Ov4; lia.
Qed.

Lemma S_shape h m:
  [0] *> RC ((m*2+1)*2^h) = MC h (2^(h+1)-1) (rd1 *> RC m).
Proof. unfold RC,MC; rw_Bin; cbv [BinaryCounter.d0 length List.repeat]; simpl_rotate; st; reflexivity. Qed.

Lemma S_step len k h m: k+(2^(h+2)-1)<2^len ->
  LC len (k+(2^(h+2)-1)) |> [0] *> RC ((m*2+1)*2^h) -->+
  LC (len+1+(h*2+1)) ((k*2+1)*2^(h*2+1)-1) |> [0] *> RC m.
Proof.
  intros HK; rewrite S_shape.
  applys_eq (Core len k h (2^(h+1)-1) m);
    [repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; flia|arith|lia].
Qed.

Lemma LC_Ov0 len i m:
  LC (len+1) 0 <| RC ((m*2+1)*2^(i+1)) -->+
  LC (len+1) ((2^len-1)*2) |> MC (i+1) (((2^i-1)*2)*2+1) (rd1 *> RC m).
Proof.
  unfold LC,RC,MC; rw_Bin; cbv [BinaryCounter.d0 length List.repeat].
  rewrite (Nat.add_comm len 1), (Nat.add_comm i 1); cbn [lpow Str_app].
  follow_rule LOv_0.
  all: arith.
Qed.

Lemma F_step len i m k: 2^(len+1)+1=k+2^(i+3) ->
  LC (len+1) 0 <| RC ((m*2+1)*2^(i+1)) -->+
  LC (len+1+1+((i+1)*2+1)) ((k*2+1)*2^((i+1)*2+1)-1) |> [0] *> RC m.
Proof.
  intros HK; follow10 LC_Ov0; apply progress_evstep.
  applys_eq (Core (len+1) k (i+1) (((2^i-1)*2)*2+1) m);
    [repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; flia|arith|arith].
Qed.

Lemma RC_Incs len k m: k<2^len ->
  LC len k |> RC m -->+ LC len 0 <| RC (m+k+1).
Proof.
  gen m; induction k; intros m HK.
  - applys_eq RC_Inc; flia.
  - follow10 RC_Inc; follow_inc LC_Inc.
    apply progress_evstep; applys_eq IHk; [flia|lia].
Qed.

Close Scope sym.
Definition Good len m := exists i a,
  m=(a*2+1)*2^(i+1) /\ i+3<=len /\ m<2^len.
Lemma good_bound len m: Good len m -> 3<=len /\ 0<m<2^len.
Proof. intros [i [a [-> [HL HM]]]]; split; [lia|arith]. Qed.
Lemma append_good len k h: 1<=len -> k<2^len ->
  Good (len+1+(h*2+1)) ((k*2+1)*2^(h*2+1)).
Proof. intros; exists (h*2),k; repeat split; try lia; arith. Qed.
Lemma F_bounds len i a k: i+3<=len -> (a*2+1)*2^(i+1)<2^len ->
  2^len+1=k+2^(i+3) ->
  k<2^len /\ 1<=k /\ a*4<=(k*2+1)*2^((i+1)*2+1)-1.
Proof.
  intros HL HM HK.
  assert (2^(i+3)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  assert (2^(i+3)<=2^((i+1)*2+1)) by (apply Nat.pow_le_mono_r; lia).
  assert (a*4<2^len) by arith.
  repeat split; arith.
Qed.
Lemma S_bounds k h a: (a*2+1)*2^h*4<=k ->
  2^(h+2)-1<=k /\
  a*4<=((k-(2^(h+2)-1))*2+1)*2^(h*2+1)-1.
Proof. intros; arith. Qed.

Inductive Config := cfgF (len m:nat) | cfgS (len k m:nat).
Definition P x := match x with
| cfgF len m => Good len m
| cfgS len k m => Good len (k+1) /\ m*4<=k
end.
Open Scope sym.
Definition to_config x := match x with
| cfgF len m => LC len 0 <| RC m
| cfgS len k m => LC len k |> [0] *> RC m
end.

Lemma closed x: P x -> exists y, to_config x -->+ to_config y /\ P y.
Proof.
  destruct x as [len m|len k m]; cbn [P to_config]; intros HP.
  - destruct HP as [i [a [-> [HL HM]]]].
    assert (HA: 2^(i+3)<=2^len) by (apply Nat.pow_le_mono_r; lia).
    set (b:=2^len+1-2^(i+3)).
    assert (HE: 2^len+1=b+2^(i+3)) by (unfold b; lia).
    destruct (F_bounds len i a b HL HM HE) as [HB [Hb Hbudget]].
    exists (cfgS (len+1+((i+1)*2+1)) ((b*2+1)*2^((i+1)*2+1)-1) a); split.
    + cbn [to_config]; applys_eq (F_step (len-1) i a b);
        [flia|flia|rewrite Nat.sub_add by lia; exact HE].
    + cbn [P]; split; [|exact Hbudget].
      applys_eq (append_good len b (i+1)); [flia|lia|exact HB].
  - destruct HP as [HG HM].
    pose proof (good_bound _ _ HG) as [HL HK].
    lowbit_cases m.
    + exists (cfgF len (k+1)); split; [|exact HG].
      cbn [to_config]; unfold RC at 1; rw_Bin; st.
      change (LC len k |> RC 0 -->+ LC len 0 <| RC (k+1)).
      apply RC_Incs; lia.
    + destruct (S_bounds k i x HM) as [Hcost Hbudget].
      set (b:=k-(2^(i+2)-1)).
      exists (cfgS (len+1+(i*2+1)) ((b*2+1)*2^(i*2+1)-1) x); split.
      * cbn [to_config]; applys_eq (S_step len b i x); [flia|unfold b; lia].
      * cbn [P]; split; [|exact Hbudget].
        applys_eq (append_good len b i); [flia|lia|unfold b; lia].
Qed.

Lemma init: c0 -->* LC 6 0 <| RC 18.
Proof. unfold LC,RC; rw_Bin; esx. Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (to_config (cfgF 6 18))).
  eapply progress_nonhalt_cond with (P:=P); [apply closed|].
  cbn [P]; exists 0%nat,4%nat; repeat split; cbn; lia.
Qed.

End TM1.

From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull BinaryCounter_v2 SimplTape ES_v2.
Require Import String ZifyNat Lia PeanoNat NArith Wf_nat.

(* SOC36_Ex4.TM4 *)
Module TM2.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String ZifyNat Lia PeanoNat NArith Wf_nat.


Definition tm := Eval compute in (TM_from_str "1RB1LA_1LA1RC_1LF1RD_0RE0RB_1RA---_1RE0LF").
Notation ld0 := <[1;1;0].
Notation ld1 := <[1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0;0;0].
Notation rd1 := [1;0;0;0;0;0].
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{A}} [1;1;1;1;1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;1;1;1;0;1;1] {{C}}> r) (at level 30).
Notation "l |2> r" := (l <* [1;1;0;1;1;0;1;1] {{B}}> r) (at level 30).
Notation "l |3> r" := (l <* [1;1;0;1;1;1;1;1] {{B}}> r) (at level 30).

Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^n <* ld1 |> [0;0;0;0] *> r.
Proof. es. Qed.
Lemma LOv_0 r n:
  ldh <* ld1^^(1+n) <| rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <* ld0 |> [0;0;0;1] *> r.
Proof. es. Qed.
Lemma ROv4 l r n:
  l |> rd1^^n *> [1;0;0;0;1;0;0;0;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*2+1) <* ld1 |2> r.
Proof. es. Qed.
Lemma ROv'_1 l r:
  l |2> rd1 *> r -->+
  l <* ld1^^2 |2> r.
Proof. es. Qed.
Lemma ROv'_0 l r k:
  l <* ld0 <* ld1^^k <* ld1 |2> rd0 *> r -->+
  l <* ld1 <* ld0^^k <* ld1 <* ld0 <* ld1 |3> r.
Proof. es. Qed.
Lemma ROv'3_1 l r k:
  l <* ld0 <* ld1^^k <* ld1 |3> rd1 *> r -->+
  l <* ld1 <* ld0^^(2+k) <* ld1 |2> r.
Proof. es. Qed.
Lemma ROv'3_0 l r k:
  l <* ld0 <* ld1^^k <* ld1 |3> rd0 *> r -->+
  l <| [0;0;0]^^(3+k) *> [1;0;0;0] *> r.
Proof. es. Qed.

Lemma ROv3 l r n:
  l |> rd1^^n *> [1;0;0;1;0;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*2+1) |3> r.
Proof. es. Qed.
Lemma ROv31 l r k n:
  l <* ld0 <* ld1^^k |> rd1^^n *> [1;0;0;1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^k |> rd0^^n *> [0;0;0;0;0;0;1] *> r.
Proof. es. Qed.
Lemma Aux3 l r:
  l |2> [1;0;0;1;0] *> r -->+ l <* ld1 <* ld0 <| r.
Proof. es. Qed.
Lemma V3 l r k:
  l <* ld0 <* ld1^^k <* ld1 |3> [1;0;0;1;0] *> r -->+
  l <* ld1 <* ld0^^(3+k) <| r.
Proof. es. Qed.

Lemma init_word:
  c0 -->* ldh <* ld0^^2 <* ld1 <* ld0 <* ld1^^2 <* ld0^^4 <| 0inf.
Proof. esx. Qed.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0;0;0;0] h n r.
Definition RM h r := MC h 0 ([0;0;1;0;0;0] *> r).

Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *;
  solve [lia|nia|flia].
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first [follow10 HX|follow100 HX];
  st; repeat (simpl_rotate || simpl_tape); finish.
Ltac solve_rule H := intros; unfold LC,RC,RM,MC; rw_Bin;
  try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Ltac exact_word H := let HX:=fresh "HX" in pose proof H as HX; gen HX;
  st; simpl_rotate; intro HX; first [exact HX|apply progress_evstep; exact HX].

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
Lemma RC_Incs len k m: k<2^len ->
  LC len k |> RC m -->+ LC len 0 <| RC (m+k+1).
Proof.
  gen m; induction k; intros m HK.
  - applys_eq RC_Inc; flia.
  - follow10 RC_Inc; follow_inc LC_Inc.
    apply progress_evstep; applys_eq IHk; [flia|lia].
Qed.
Lemma RC_finish len k: 0<k<2^len ->
  LC len k <| 0inf -->+ LC len 0 <| RC k.
Proof.
  intros HK; destruct k; [lia|].
  eapply evstep_progress_trans; [apply progress_evstep,LC_Inc; lia|].
  change (LC len k |> RC 0 -->+ LC len 0 <| RC (S k)).
  applys_eq RC_Incs; [flia|lia].
Qed.

(* Increment/decrement shapes, independent of head direction. *)
Lemma LC_split len k: 1+k<2^len -> exists l n,
  LC len (1+k)=l <* ld0 <* ld1^^n /\ LC len k=l <* ld1 <* ld0^^n.
Proof.
  unfold LC,BinDec; intros HK.
  assert (HE: Pos.of_nat (2^(len+1)-1-k)=Pos.succ (Pos.of_nat (2^(len+1)-1-(1+k)))) by arith.
  rewrite HE.
  eapply not_full_Inc.
  rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len); [rewrite pow2'_spec'; arith|arith].
Qed.

Lemma U_odd len k r: k<2^len ->
  LC len k |2> rd1 *> r -->+ LC (len+2) (k*4) |2> r.
Proof.
  replace (len+2) with (len+1+1) by lia.
  replace (k*4) with (k*2*2) by lia; solve_rule ROv'_1.
Qed.
Lemma U_even len k r: (k+1)*2<2^(len+1) ->
  LC (len+1) ((k+1)*2) |2> rd0 *> r -->+
  LC (len+3) (k*8+2) |3> r.
Proof.
  intros HK; destruct (LC_split len k) as [l [n [HA HB]]]; [arith|].
  replace (len+3) with (len+1+1+1) by lia.
  replace (k*8+2) with ((k*2*2+1)*2) by lia.
  unfold LC; rw_Bin; try solve[arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule ROv'_0.
Qed.
Lemma V_odd len k r: (k+1)*2<2^(len+1) ->
  LC (len+1) ((k+1)*2) |3> rd1 *> r -->+
  LC (len+3) (k*8+6) |2> r.
Proof.
  intros HK; destruct (LC_split len k) as [l [n [HA HB]]]; [arith|].
  replace (len+3) with (len+1+1+1) by lia.
  replace (k*8+6) with (((k*2+1)*2+1)*2) by lia.
  unfold LC; rw_Bin; try solve[arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule ROv'3_1.
Qed.
Lemma V_last len k: (k+1)*2<2^(len+1) ->
  LC (len+1) ((k+1)*2) |3> [1;0;0;1] *> 0inf -->+
  LC (len+3) (k*8+7) <| 0inf.
Proof.
  intros HK; destruct (LC_split len k) as [l [n [HA HB]]]; [arith|].
  replace (len+3) with (len+1+1+1) by lia.
  replace (k*8+7) with (((k*2+1)*2+1)*2+1) by lia.
  unfold LC; rw_Bin; try solve[arith]; unfold LC in HA,HB; unfold Sym in *.
  rewrite (Nat.add_comm k 1),HA,HB; follow_rule (V3 l 0inf n).
Qed.
Lemma V_even len k r: k<2^len ->
  LC (len+2) (k*4+2) |3> rd0 *> r -->+
  LC len k <| [0;0;0]^^3 *> [1;0;0;0] *> r.
Proof.
  replace (len+2) with (len+1+1) by lia.
  replace (k*4+2) with ((k*2+1)*2) by lia.
  solve_rule (ROv'3_0 (LC len k) r 0).
Qed.
Lemma U_last len k: k<2^len ->
  LC len k |2> [1;0;0;1] *> 0inf -->+ LC (len+2) (k*4+1) <| 0inf.
Proof.
  replace (len+2) with (len+1+1) by lia.
  replace (k*4+1) with (k*2*2+1) by lia.
  solve_rule (Aux3 (LC len k) 0inf).
Qed.
Lemma U_01 len k r: (k+1)*2<2^(len+1) ->
  LC (len+1) ((k+1)*2) |2> rd0 *> rd1 *> r -->+
  LC (len+5) (k*32+6) |2> r.
Proof.
  intros HK; follow10 (U_even len k (rd1 *> r) HK).
  apply progress_evstep; applys_eq (V_odd (len+2) (k*4) r); try solve[flia]; arith.
Qed.
Lemma U_01_last len k: (k+1)*2<2^(len+1) ->
  LC (len+1) ((k+1)*2) |2> rd0 *> [1;0;0;1] *> 0inf -->+
  LC (len+5) (k*32+7) <| 0inf.
Proof.
  intros HK; follow10 (U_even len k ([1;0;0;1] *> 0inf) HK).
  apply progress_evstep; applys_eq (V_last (len+2) (k*4)); try solve[flia]; arith.
Qed.
Lemma U_00 len k r: k*2+6<2^(len+1) ->
  LC (len+1) (k*2+6) |2> rd0 *> rd0 *> r -->+
  LC (len+1) (k*2) |> RM 1 r.
Proof.
  intros HK.
  eapply progress_evstep_trans;
    [applys_eq (U_even len (k+2)); [flia|lia]|].
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (V_even (len+1) (k*2+4) r); try solve[flia]; arith|].
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_Inc (len+1) (k*2+3)); [flia|lia]|].
  change (LC (len+1) (k*2+3) |> MC 1 3 ([0;0;1;0;0;0] *> r) -->*
    LC (len+1) (k*2) |> RM 1 r).
  follow MC_Incs; try finish; arith.
Qed.

Lemma RM_odd_word l h r:
  l |> RM h (rd1 *> r) -->+ l <* ld1 <* ld0^^(h*2+2) <* ld1 |2> r.
Proof.
  unfold RM,MC; rw_Bin; follow10 ROv3.
  exact_word (ROv'3_1 l r (h*2)).
Qed.
Lemma RM_last_word l h:
  l |> RM h ([1;0;0;1] *> 0inf) -->+
  l <* ld1 <* ld0^^(h*2+3) <| 0inf.
Proof.
  unfold RM,MC; rw_Bin; follow10 ROv3.
  exact_word (V3 l 0inf (h*2)).
Qed.
Lemma RM_even_word l h r:
  l |> RM h (rd0 *> r) -->+
  l <| MC (h+1) (2^(h+2)-1) ([0;0;1;0;0;0] *> r).
Proof.
  replace (h+2) with (h+1+1) by lia.
  unfold RM,MC; rw_Bin; follow10 ROv3.
  exact_word (ROv'3_0 l r (h*2)).
Qed.
Lemma R_odd len k h r: k<2^len ->
  LC len k |> RM h (rd1 *> r) -->+
  LC (len+h*2+4) ((k*2+1)*2^(h*2+3)-2) |2> r.
Proof.
  replace (len+h*2+4) with (len+1+(h*2+2)+1) by lia.
  replace ((k*2+1)*2^(h*2+3)-2) with
    (((k*2+1)*2^(h*2+2)-1)*2) by arith.
  intros HK; unfold LC; rw_Bin; try solve[arith].
  follow_rule RM_odd_word.
Qed.
Lemma R_last len k h: k<2^len ->
  LC len k |> RM h ([1;0;0;1] *> 0inf) -->+
  LC (len+h*2+4) ((k*2+1)*2^(h*2+3)-1) <| 0inf.
Proof.
  replace (len+h*2+4) with (len+1+(h*2+3)) by lia.
  intros HK; unfold LC; rw_Bin; try solve[arith].
  follow_rule RM_last_word.
Qed.
Lemma R_even len k h r: k+2^(h+2)<2^len ->
  LC len (k+2^(h+2)) |> RM h (rd0 *> r) -->+
  LC len k |> RM (h+1) r.
Proof.
  intros HK; follow10 RM_even_word.
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_Inc len (k+(2^(h+2)-1))); [flia|lia]|].
  unfold RM; follow MC_Incs; try finish; arith.
Qed.
Definition M4 h n r := MC h n ([0;0;0;1;0;0;0;0;0] *> r).
Lemma M4_start h r:
  [0;0;0;0] *> rd0^^h *> rd1 *> r = M4 h (2^(h+1)-1) r.
Proof. unfold M4,MC; rw_Bin; cbv [d0 List.length List.repeat]; st; simpl_rotate; reflexivity. Qed.
Lemma M4_start2 h r:
  [0;0;0;0;0;0;1;0;0;0] *> rd0^^(h+1) *> rd1 *> r =
  M4 (h+2) (2^(h+3)-3) r.
Proof.
  replace (h+2) with (h+1+1) by lia.
  replace (2^(h+3)-3) with (((2^(h+1)-1)*2)*2+1) by arith.
  unfold M4,MC; rw_Bin; try solve[arith].
  st; simpl_rotate; reflexivity.
Qed.
Lemma M4_Ov len k h r: k<2^len ->
  LC len k |> M4 h 0 r -->+
  LC (len+h*2+3) ((k*2+1)*2^(h*2+2)-2) |2> r.
Proof.
  replace (len+h*2+3) with (len+1+(h*2+1)+1) by lia.
  replace ((k*2+1)*2^(h*2+2)-2) with
    (((k*2+1)*2^(h*2+1)-1)*2) by arith.
  intros HK; unfold M4,LC,MC; rw_Bin; try solve[arith].
  exact_word (ROv4 (LC len k) r h).
Qed.
Lemma LC_Ov1 len r:
  LC len 0 <| rd1 *> r -->+ LC (len+1) ((2^len-1)*2) |> [0;0;0;0] *> r.
Proof. solve_rule LOv_1. Qed.
Lemma LC_Ov0 len r:
  LC (len+1) 0 <| rd0 *> r -->+
  LC (len+2) ((2^len-1)*4+1) |> [0;0;0;1] *> r.
Proof.
  replace (len+2) with (len+1+1) by lia.
  replace ((2^len-1)*4+1) with ((2^len-1)*2*2+1) by lia.
  unfold LC; rw_Bin; try solve[arith]; exact_word (LOv_0 r len).
Qed.
Lemma R31_decr len k r: 1+k<2^len ->
  LC len (1+k) |> [1;0;0;1] *> rd1 *> r -->+
  LC len k |> [0;0;0;0;0;0;1;0;0;0] *> r.
Proof.
  intros HK; destruct (LC_split len k HK) as [l [n [HA HB]]].
  rewrite HA,HB; exact_word (ROv31 l ([0;0;0] *> r) n 0).
Qed.
Lemma G_prefix len r: 1<=len ->
  LC (len+1) 0 <| rd0 *> rd1 *> r -->+
  LC (len+2) (2^(len+2)-5) |> [0;0;0;0;0;0;1;0;0;0] *> r.
Proof.
  intros HL; assert (HP: 2^1<=2^len) by (apply Nat.pow_le_mono_r; lia).
  follow10 LC_Ov0.
  follow100 (RInc (LC (len+2) ((2^len-1)*4+1)) ([0;0;1] *> rd1 *> r) 0).
  eapply evstep_trans; [apply progress_evstep;
    applys_eq (LC_Inc (len+2) ((2^len-1)*4)); try solve[flia]; arith|].
  apply progress_evstep; applys_eq (R31_decr (len+2) (2^(len+2)-5) r);
    try solve[flia]; arith.
Qed.
Lemma F_entry len h b r: b+2^(h+1)+1=2^(len+1) ->
  LC len 0 <| rd1 *> rd0^^h *> rd1 *> r -->+
  LC (len+h*2+4) ((b*2+1)*2^(h*2+2)-2) |2> r.
Proof.
  intros HB; follow10 LC_Ov1; rewrite M4_start.
  eapply evstep_trans; [unfold M4;
    applys_eq (MC_Incs (len+1) b h (2^(h+1)-1)); try solve[flia]; arith|].
  apply progress_evstep; applys_eq (M4_Ov (len+1) b h r); try solve[flia]; arith.
Qed.
Lemma G_entry len h b r: 1<=len -> b+2^(h+3)+2=2^(len+2) ->
  LC (len+1) 0 <| rd0 *> rd1 *> rd0^^(h+1) *> rd1 *> r -->+
  LC (len+h*2+9) ((b*2+1)*2^(h*2+6)-2) |2> r.
Proof.
  intros HL HB; follow10 (G_prefix len (rd0^^(h+1) *> rd1 *> r) HL).
  rewrite M4_start2.
  eapply evstep_trans; [unfold M4;
    applys_eq (MC_Incs (len+2) b (h+2) (2^(h+3)-3)); try solve[flia]; arith|].
  apply progress_evstep; applys_eq (M4_Ov (len+2) b (h+2) r); try solve[flia]; arith.
Qed.

Lemma MC_finish len k h n r: k<2^len -> n+k<2^(h+1) ->
  LC len k <| MC h (n+k) r -->* LC len 0 <| MC h n r.
Proof.
  induction k; intros HK HN; [applys_eq evstep_refl; flia|].
  follow_inc LC_Inc; rewrite Nat.add_succ_r; follow_inc MC_Inc.
  follow IHk; try finish; lia.
Qed.
Lemma R_zero_last len k h: k<2^len -> k<2^(h+2) ->
  LC len k |> RM h 0inf -->+
  LC len 0 <| MC (h+1) (2^(h+2)-1-k) ([0;0;1;0;0;0] *> 0inf).
Proof.
  intros HK HB.
  assert (HZ: rd0 *> 0inf=0inf) by solve_const0_eq.
  pose proof (RM_even_word (LC len k) h 0inf) as H; rewrite HZ in H; follow10 H.
  applys_eq (MC_finish len k (h+1) (2^(h+2)-1-k)); try solve[flia]; arith.
Qed.
(* Both right-tail conventions, with a distinct final marked digit. *)
Inductive Num: bool->nat->side->Prop :=
| Num_Z: Num false 0 0inf
| Num_T: Num true 1 ([1;0;0;1] *> 0inf)
| Num_E b n r: 0<n -> Num b n r -> Num b (n*2) (rd0 *> r)
| Num_I b n r: Num b n r -> Num b (n*2+1) (rd1 *> r).

Lemma Num_even_inv b n r: 0<n -> Num b (n*2) r ->
  exists r', Num b n r' /\ r=rd0 *> r'.
Proof.
  intros Hn H; inverts H; try lia.
  match goal with HN: Num _ _ _ |- _ =>
    eexists; split; [applys_eq HN; flia|reflexivity] end.
Qed.
Lemma Num_odd_inv b n r: 0<n -> Num b (n*2+1) r ->
  exists r', Num b n r' /\ r=rd1 *> r'.
Proof.
  intros Hn H; inverts H; try lia.
  match goal with HN: Num _ _ _ |- _ =>
    eexists; split; [applys_eq HN; flia|reflexivity] end.
Qed.
Lemma Num_pow_inv b n i r: 0<n -> Num b ((n*2+1)*2^i) r ->
  exists r', Num b n r' /\ r=rd0^^i *> rd1 *> r'.
Proof.
  intros Hn; gen r; induction i; intros r H.
  - replace ((n*2+1)*2^0) with (n*2+1) in H by lia.
    apply Num_odd_inv in H; [exact H|lia].
  - replace ((n*2+1)*2^(S i)) with (((n*2+1)*2^i)*2) in H by arith.
    destruct (Num_even_inv b ((n*2+1)*2^i) r ltac:(arith) H) as [s [HS ->]].
    destruct (IHi s HS) as [r' [HN ->]].
    exists r'; split; [exact HN|cbn [lpow]; simpl_tape; reflexivity].
Qed.
Lemma Num_RC n: Num false n (RC n).
Proof.
  induction n using lt_wf_ind.
  destruct (Nat.eq_dec n 0) as [->|HN]; [unfold RC; rw_Bin; constructor|].
  divmod2_cases n; unfold RC; rw_Bin; cbv [d0 List.length List.repeat].
  - apply Num_E; [lia|apply H; lia].
  - apply Num_I; apply H; lia.
Qed.

Lemma MC_low0 h n r: n<2^(h+1) ->
  MC (h+1) (n*2+1) r=rd0 *> MC h n r.
Proof.
  intros Hn; divmod2_cases n; unfold MC; rw_Bin; try solve[arith];
    st; simpl_rotate; reflexivity.
Qed.
Lemma MC_low1 h n r: n<2^(h+1) ->
  MC (h+1) (n*2) r=rd1 *> MC h n r.
Proof.
  intros Hn; divmod2_cases n; unfold MC; rw_Bin; try solve[arith];
    st; simpl_rotate; reflexivity.
Qed.
Lemma Num_MC h m: 2^h<=m<2^(h+1) ->
  Num true m (MC h (2^(h+1)-1-m) ([0;0;1;0;0;0] *> 0inf)).
Proof.
  gen m; induction h; intros m HM.
  - replace m with 1%nat by (cbn in HM; lia).
    unfold MC; rw_Bin; cbn [Str_app]; repeat rewrite <-(const_unfold _ 0).
    change (Num true 1 ([1;0;0;1] *> 0inf)); constructor.
  - replace (S h) with (h+1) in * by lia.
    destruct (divmod2 m) as [m' x ->|m' x ->].
    + replace (2^(h+1+1)-1-x*2) with ((2^(h+1)-1-x)*2+1) by arith.
      rewrite MC_low0 by arith; apply Num_E; [arith|apply IHh; arith].
    + replace (2^(h+1+1)-1-(x*2+1)) with ((2^(h+1)-1-x)*2) by arith.
      rewrite MC_low1 by arith; apply Num_I,IHh; arith.
Qed.

(* Highest two bits are 11; no log2 is needed in the proof. *)
Close Scope sym.
Definition High m := exists i, 2^i*3<=m<2^i*4.
Lemma High_bound m: High m -> 3<=m.
Proof. intros [i H]; arith. Qed.
Lemma High_even m: High (m*2) -> High m.
Proof.
  intros [i H]; destruct i; [cbn in H; lia|].
  exists i; cbn [Nat.pow] in H; nia.
Qed.
Lemma High_odd m: High (m*2+1) -> m=1 \/ High m.
Proof.
  intros [i H]; destruct i; [left; cbn in H; lia|].
  right; exists i; cbn [Nat.pow] in H; nia.
Qed.
Lemma High_pow m i: High (m*2^i) -> High m.
Proof.
  induction i; intros H; [applys_eq H; flia|].
  apply IHi,High_even; applys_eq H; arith.
Qed.
Definition FB len m := 4<=len /\ m mod 2=1 /\ 2^len*3<m*4 /\ m<2^len.
Definition GB len m := 6<=len /\ m mod 8=2 /\ 2^len+8<m*4 /\ m*2<2^len.
Definition UB len k m D := 4<=len /\ k<2^len /\ k mod 2=0 /\
  2^len=k+2+D /\ 0<D /\ (D+m*2+4)*4<=2^len.
Definition RB len k h m D := 4<=len /\ 1<=h /\ k<2^len /\ k mod 2=0 /\
  2^len=k+2^(h+2)+D /\ 0<D /\ (D+2^(h+2)*m+4)*4<=2^len.
Ltac bounds := intros; unfold FB,GB,UB,RB in *;
  repeat match goal with H:_ /\ _ |- _ => destruct H end;
  repeat split; arith.

Lemma UB_small len k m D: UB len k m D -> 6<=k.
Proof. bounds. Qed.
Lemma UB_odd len k m D: UB len k (m*2+1) D ->
  UB (len+2) (k*4) m (D*4+6).
Proof. bounds. Qed.
Lemma UB_01 len k m D: UB len (k*2+2) (m*4+2) D ->
  UB (len+4) (k*32+6) m (D*16+56).
Proof. bounds. Qed.
Lemma UB_00 len k m D: UB len (k*2+6) (m*4) D ->
  RB len (k*2) 1 m D.
Proof. bounds. Qed.
Lemma RB_even len k h m D: RB len (k+2^(h+2)) h (m*2) D ->
  RB len k (h+1) m D.
Proof. bounds. Qed.
Lemma RB_odd len k h m D: RB len k h (m*2+1) D ->
  UB (len+h*2+4) ((k*2+1)*2^(h*2+3)-2) m
     ((D*2+2^(h+3)-1)*2^(h*2+3)).
Proof. bounds. Qed.
Lemma UB_last len k D: UB len k 1 D -> FB (len+2) (k*4+1).
Proof. bounds. Qed.
Lemma UB_01_last len k D: UB len (k*2+2) 2 D -> FB (len+4) (k*32+7).
Proof. bounds. Qed.
Lemma RB_last len k h D: RB len k h 1 D ->
  FB (len+h*2+4) ((k*2+1)*2^(h*2+3)-1).
Proof. bounds. Qed.

Lemma RB_exit len k h D: RB len k h 0 D -> D mod 8=6 -> k<2^(h+2) ->
  len=h+3 /\ GB len k.
Proof.
  intros [HL [Hh [HK [HE [HD [HD0 HB]]]]]] HM HS.
  assert (Hlo: h+3<=len).
  { destruct (Nat.le_gt_cases len (h+2)); [|lia].
    assert (2^len<=2^(h+2)) by (apply Nat.pow_le_mono_r; lia); lia. }
  assert (Hlen: len=h+3).
  { destruct (Nat.le_gt_cases len (h+3)); [lia|].
    assert (2^(h+4)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith. }
  split; [exact Hlen|].
  assert (HL6: 6<=len).
  { destruct (Nat.le_gt_cases len 5); [|lia].
    assert (2^len<=2^5) by (apply Nat.pow_le_mono_r; lia); arith. }
  subst len; destruct h; [lia|]; unfold GB; repeat split; arith.
Qed.
Lemma UB_Deven len k m D: UB len k m D -> D mod 2=0.
Proof. destruct len; bounds. Qed.
Lemma FB_high len a: FB len (a*2+1) -> High a.
Proof.
  intros [HL [HE [HB HM]]]; destruct len as [|[|[|len]]]; try lia.
  exists len; cbn [Nat.pow] in *; nia.
Qed.
Lemma GB_notpow len h a: GB len ((a*2+1)*2^(h+3)+2) -> 0<a.
Proof.
  intros [HL [HE [HB HM]]]; destruct a; [|lia].
  destruct (Nat.le_gt_cases len (h+4)).
  - assert (2^len<=2^(h+4)) by (apply Nat.pow_le_mono_r; lia); arith.
  - assert (2^(h+5)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith.
Qed.
Lemma FB_entry len h a b: 4<=len -> 0<a ->
  (a*2+1)*2^(h+1)+1<2^len -> b+2^(h+1)+1=2^(len+1) ->
  UB (len+h*2+4) ((b*2+1)*2^(h*2+2)-2) a
     ((2^(h+2)+1)*2^(h*2+2)).
Proof. bounds. Qed.
Lemma GB_entry len h a b: 6<=len -> 0<a ->
  ((a*2+1)*2^(h+3)+2)*2<2^len -> b+2^(h+3)+2=2^(len+1) ->
  UB (len+h*2+8) ((b*2+1)*2^(h*2+6)-2) a
     ((2^(h+4)+3)*2^(h*2+6)).
Proof. bounds. Qed.

Definition UL (b:bool) m D := if b then True else m=1 \/ High m \/ (m=0 /\ D mod 8=6).
Definition RL (b:bool) m D := if b then True else High m \/ (m=0 /\ D mod 8=6).
Lemma UL_odd b m D: D mod 2=0 -> UL b (m*2+1) D -> UL b m (D*4+6).
Proof.
  destruct b; cbn [UL]; [auto|].
  intros HE [H|[H|[H HD]]].
  - right; right; split; [lia|].
    pose proof (Nat.Div0.div_mod D 2).
    replace (D*4+6) with ((D/2)*8+6) by lia.
    rewrite Nat.Div0.add_mod, Nat.Div0.mod_mul; reflexivity.
  - destruct (High_odd _ H); auto.
  - lia.
Qed.
Lemma UL_01 b m D: UL b (m*4+2) D -> UL b m (D*16+56).
Proof.
  destruct b; cbn [UL]; [auto|].
  intros [H|[H|[H HD]]]; try lia.
  assert (HH: High (m*2+1)) by (apply High_even; applys_eq H; flia).
  destruct (High_odd _ HH); auto.
Qed.
Lemma UL_00 b m D: UL b (m*4) D -> RL b m D.
Proof.
  destruct b; cbn [UL RL]; [auto|].
  intros [H|[H|[H HD]]]; try lia.
  - left; apply High_even,High_even; applys_eq H; flia.
Qed.
Lemma RL_even b m D: RL b (m*2) D -> RL b m D.
Proof.
  destruct b; cbn [RL]; [auto|].
  intros [H|[H HD]]; [left; apply High_even,H|right; split; lia].
Qed.
Lemma RL_odd b m D D': RL b (m*2+1) D -> UL b m D'.
Proof.
  destruct b; cbn [RL UL]; [auto|].
  intros [H|[H HD]]; [destruct (High_odd _ H); auto|lia].
Qed.
Lemma RL_zero D: RL false 0 D -> D mod 8=6.
Proof. intros [H|[H HD]]; try lia; pose proof (High_bound _ H); lia. Qed.
Open Scope sym.

Inductive P: Q*tape -> Prop :=
| PF len m r: Num false m r -> FB len m -> P (LC len 0 <| r)
| PG len m r: Num true m r -> GB len m -> P (LC len 0 <| r)
| PU b len k m r D: Num b m r -> UB len k m D -> UL b m D ->
    P (LC len k |2> r)
| PR b len k h m r D: Num b m r -> RB len k h m D -> RL b m D ->
    P (LC len k |> RM h r).

Lemma F_step len m r: Num false m r -> FB len m ->
  exists c, LC len 0 <| r -->+ c /\ P c.
Proof.
  intros HN HB; pose proof HB as [HL [HE [HV HM]]].
  destruct (divmod2 m) as [m' a ->|m' a ->]; [lia|].
  pose proof (FB_high _ _ HB) as HH.
  destruct (Num_odd_inv false a r ltac:(apply High_bound in HH; lia) HN)
    as [s [HS ->]].
  lowbit_cases a; [apply High_bound in HH; lia|].
  apply High_pow in HH; apply High_odd in HH.
  assert (HX: 0<x) by (destruct HH as [->|HH]; [lia|apply High_bound in HH; lia]).
  destruct (Num_pow_inv false x i s HX HS) as [r' [HN' ->]].
  assert (HEq: (2^(len+1)-2^(i+1)-1)+2^(i+1)+1=2^(len+1)) by arith.
  eexists; split; [apply F_entry,HEq|].
  eapply PU; [exact HN'|apply FB_entry; try assumption; arith|cbn [UL]; tauto].
Qed.

Lemma G_step len m r: Num true m r -> GB len m ->
  exists c, LC len 0 <| r -->+ c /\ P c.
Proof.
  intros HN HB; pose proof HB as [HL [HE [HV HM]]].
  pose proof (Nat.Div0.div_mod m 8) as HQ.
  set (a:=m/8) in HQ; clearbody a.
  assert (Hm: m=a*8+2) by lia; clear HQ; subst m.
  assert (Ha: 0<a) by (destruct a; arith).
  destruct (Num_even_inv true (a*4+1) r ltac:(lia) ltac:(applys_eq HN; flia))
    as [s [HS ->]].
  destruct (Num_odd_inv true (a*2) s ltac:(lia) ltac:(applys_eq HS; flia)) as [t [HT ->]].
  destruct (Num_even_inv true a t Ha HT) as [u [HU ->]].
  lowbit_cases a; [lia|].
  assert (HX: 0<x) by (apply (GB_notpow len i); applys_eq HB; arith).
  destruct (Num_pow_inv true x i u HX HU) as [r' [HN' ->]].
  set (b:=2^(len+1)-2^(i+3)-2).
  assert (HEq: b+2^(i+3)+2=2^(len+1)) by (unfold b; arith).
  exists (LC (len+i*2+8) ((b*2+1)*2^(i*2+6)-2) |2> r'); split.
  - applys_eq (G_entry (len-1) i b r');
      try solve[flia]; try lia.
    + rewrite Nat.sub_add by lia; replace (i+1) with (S i) by lia.
      cbn [lpow]; simpl_tape; reflexivity.
    + applys_eq HEq; flia.
  - eapply PU; [exact HN'|apply GB_entry; try assumption; arith|exact I].
Qed.

Lemma toF len k c: FB len k -> c -->+ LC len k <| 0inf ->
  exists c', c -->+ c' /\ P c'.
Proof.
  intros HB HS; exists (LC len 0 <| RC k); split.
  - eapply progress_trans; [exact HS|apply RC_finish; bounds].
  - apply PF with (m:=k); [apply Num_RC|exact HB].
Qed.

Lemma U00_step b len k m r D: Num b m r ->
  UB (len+1) (k*2+6) (m*4) D -> UL b (m*4) D ->
  exists c, LC (len+1) (k*2+6) |2> rd0 *> rd0 *> r -->+ c /\ P c.
Proof.
  intros HN HB HL; eexists; split; [apply U_00; bounds|].
  eapply PR; [exact HN|apply UB_00,HB|apply UL_00,HL].
Qed.
Lemma U01_step b len k m r D: Num b m r ->
  UB (len+1) (k*2+2) (m*4+2) D -> UL b (m*4+2) D ->
  exists c, LC (len+1) (k*2+2) |2> rd0 *> rd1 *> r -->+ c /\ P c.
Proof.
  intros HN HB HL; eexists; split;
    [applys_eq (U_01 len k r); [flia|bounds]|].
  eapply PU; [exact HN|applys_eq (UB_01 (len+1) k m D); [flia|exact HB]|apply UL_01,HL].
Qed.

Lemma U_step b len k m r D: Num b m r -> UB len k m D -> UL b m D ->
  exists c, LC len k |2> r -->+ c /\ P c.
Proof.
  intros HN HB HL; pose proof (UB_small _ _ _ _ HB) as HK.
  pose proof HB as [Hlen [Hk [He HD]]].
  destruct len as [|len]; [lia|]; replace (S len) with (len+1) in * by lia.
  destruct (divmod2 k) as [k' a ->|k' a ->]; [|lia].
  destruct a as [|[|[|a]]]; try lia.
  replace (S (S (S a))*2) with (a*2+6) in * by lia.
  destruct HN as [| |b m r Hm HN|b m r HN].
  - assert (HZ: rd0 *> 0inf=0inf) by solve_const0_eq.
    pose proof (U00_step false len a 0 0inf D Num_Z HB HL) as HT.
    repeat rewrite HZ in HT; exact HT.
  - eapply toF; [eapply UB_last; exact HB|apply U_last; lia].
  - destruct HN as [| |b m r Hm' HN|b m r HN]; [lia| | |].
    + eapply toF with (k:=(a+2)*32+7).
      * applys_eq (UB_01_last (len+1) (a+2) D); try solve[flia].
        applys_eq HB; flia.
      * applys_eq (U_01_last len (a+2)); try solve[flia]; lia.
    + apply (U00_step b len a m r D);
        [exact HN|applys_eq HB; flia|applys_eq HL; flia].
    + replace (a*2+6) with ((a+2)*2+2) by lia.
      apply (U01_step b len (a+2) m r D);
        [exact HN|applys_eq HB; flia|applys_eq HL; flia].
  - eexists; split; [apply U_odd; lia|].
    eapply PU; [exact HN|apply UB_odd,HB|apply UL_odd; [eapply UB_Deven; exact HB|exact HL]].
Qed.

Lemma R0_step len k h D: RB len k h 0 D -> RL false 0 D ->
  exists c, LC len k |> RM h 0inf -->+ c /\ P c.
Proof.
  intros HB HL; pose proof HB as [Hlen [Hh [Hk HD]]].
  destruct (Nat.le_gt_cases (2^(h+2)) k) as [HS|HS].
  - assert (HZ: rd0 *> 0inf=0inf) by solve_const0_eq.
    exists (LC len (k-2^(h+2)) |> RM (h+1) 0inf); split.
    + pose proof (R_even len (k-2^(h+2)) h 0inf ltac:(lia)) as HT.
      rewrite HZ in HT; applys_eq HT; flia.
    + eapply PR; [constructor| |exact HL].
      apply (RB_even len (k-2^(h+2)) h 0 D); applys_eq HB; flia.
  - destruct (RB_exit _ _ _ _ HB (RL_zero _ HL) HS) as [Hlh HG].
    eexists; split; [apply R_zero_last; assumption|].
    apply PG with (m:=k); [applys_eq (Num_MC (h+1) k); try solve[flia]|exact HG].
    destruct HG as [HL6 [HE [HV HM]]]; subst len; arith.
Qed.

Lemma R_step b len k h m r D: Num b m r -> RB len k h m D -> RL b m D ->
  exists c, LC len k |> RM h r -->+ c /\ P c.
Proof.
  intros HN HB HL; pose proof HB as [Hlen [Hh [Hk [He [HD [HD0 HB0]]]]]].
  destruct HN as [| |b m r Hm HN|b m r HN].
  - apply (R0_step _ _ _ _ HB HL).
  - eapply toF; [eapply RB_last; exact HB|apply R_last; assumption].
  - assert (HS: 2^(h+2)<=k) by arith.
    exists (LC len (k-2^(h+2)) |> RM (h+1) r); split.
    + applys_eq (R_even len (k-2^(h+2)) h r); [flia|lia].
    + eapply PR; [exact HN| |apply RL_even,HL].
      apply (RB_even len (k-2^(h+2)) h m D); applys_eq HB; flia.
  - eexists; split; [apply R_odd; assumption|].
    eapply PU; [exact HN|apply RB_odd,HB|eapply RL_odd; exact HL].
Qed.

Lemma closed c: P c -> exists c', c -->+ c' /\ P c'.
Proof.
  intros H; destruct H.
  - eapply F_step; eassumption.
  - eapply G_step; eassumption.
  - eapply U_step; eassumption.
  - eapply R_step; eassumption.
Qed.

Lemma init_counter: c0 -->* LC 10 847 <| 0inf.
Proof. unfold LC; rw_Bin; exact_word init_word. Qed.

Lemma P_nonhalt c: P c -> ~halts tm c.
Proof.
  intros H; eapply progress_nonhalt_cond with (C:=fun c => c) (P:=P);
    [apply closed|exact H].
Qed.
Lemma empty_nonhalt len k: FB len k -> ~halts tm (LC len k <| 0inf).
Proof.
  intros HB; eapply multistep_nonhalt;
    [apply progress_evstep,RC_finish; bounds|].
  apply P_nonhalt; apply PF with (m:=k); [apply Num_RC|exact HB].
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init_counter|].
  apply empty_nonhalt; unfold FB; cbn; lia.
Qed.

End TM2.

(* SOC36_Ex4.TM5 *)
Module TM3.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String ZifyNat Lia PeanoNat NArith Wf_nat.


Import TM2.
Definition tm := Eval compute in (TM_from_str "1LB1RC_1RA1LB_1LD1RF_1RE0LD_1RB---_0RE0RA").
Definition rename q := match q with A=>B | B=>A | C=>C | D=>F | E=>E | F=>D end.
Lemma same_rules: Perm TM2.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Lemma init: c0 -[tm]->* TM2.LC 13 7481 <{{B}} [1;1;1;1;1;1;0] *> 0inf.
Proof.
  replace (TM2.LC 13 7481) with
    (ldh <* ld0^^3 <* ld1 <* ld0 <* ld1^^2
     <* ld0^^3 <* ld1^^2 <* ld0) by (vm_compute; reflexivity).
  esx.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM2.tm tm rename A _); [apply same_rules|].
  apply TM2.empty_nonhalt; unfold TM2.FB; repeat apply conj;
    first [apply Nat.leb_le|apply Nat.ltb_lt|idtac]; vm_compute; reflexivity.
Qed.
End TM3.

(* SOC36_Ex4.TM6 *)
Module TM4.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String ZifyNat Lia PeanoNat NArith Wf_nat.


Import TM2.
Definition tm := Eval compute in (TM_from_str "1RB---_1RC1LB_1LB1RD_1LF1RE_0RA0RC_1RA0LF").
Definition rename q := match q with A=>B | B=>C | C=>D | D=>E | E=>A | F=>F end.
Lemma same_rules: Perm TM2.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Lemma init: c0 -[tm]->* TM2.LC 14 15801 <{{B}} [1;1;1;1;1;1;0] *> 0inf.
Proof.
  replace (TM2.LC 14 15801) with
    (ldh <* ld0^^4 <* ld1 <* ld0^^2 <* ld1
     <* ld0^^3 <* ld1^^2 <* ld0) by (vm_compute; reflexivity).
  esx.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM2.tm tm rename A _); [apply same_rules|].
  apply TM2.empty_nonhalt; unfold TM2.FB; repeat apply conj;
    first [apply Nat.leb_le|apply Nat.ltb_lt|idtac]; vm_compute; reflexivity.
Qed.
End TM4.

(* SOC36_Ex4.TM7 *)
Module TM5.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter BusyCoq.BinaryCounterFull BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import String ZifyNat Lia PeanoNat NArith Wf_nat.


Import TM2.
Definition tm := Eval compute in (TM_from_str "1RB0LA_1RC---_1RD1LC_1LC1RE_1LA1RF_0RB0RD").
Definition rename q := match q with A=>C | B=>D | C=>E | D=>F | E=>B | F=>A end.
Lemma same_rules: Perm TM2.tm tm rename.
Proof. split; intros [] []; cbn; intros; try congruence; inversion H; reflexivity. Qed.
Lemma init: c0 -[tm]->*
  TM2.LC 20 (2^20-178) <* [1;1;0;1;1;0;1;1] {{D}}> TM2.RC 1863.
Proof.
  replace (TM2.LC 20 (2^20-178)) with
    (ldh <* ld0^^12 <* ld1 <* ld0 <* ld1^^2
     <* ld0^^3 <* ld1) by (vm_compute; reflexivity).
  unfold TM2.RC; cbv [BinInc]; esx.
Qed.
Lemma region len: 14<=len -> TM2.UB len (2^len-178) 1863 176.
Proof.
  intros HL; destruct len; [lia|].
  assert (HB: 128*128<=2^(S len)) by
    (change (2^14<=2^(S len)); apply Nat.pow_le_mono_r; lia).
  unfold TM2.UB; cbn [Nat.pow] in *; repeat apply conj; lia.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply (@perm_nonhalt' TM2.tm tm rename B _); [apply same_rules|].
  apply TM2.P_nonhalt; eapply TM2.PU with (D:=176);
    [apply TM2.Num_RC|apply region; lia|].
  unfold TM2.UL; right; left; exists 9; cbn; lia.
Qed.
End TM5.
