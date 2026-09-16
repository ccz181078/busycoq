(* Consolidated checked proofs. See SOC_FT7_CONSOLIDATION.md for numbering. *)

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* Shared definitions from SOC24_R3.v. *)
Module SOC24_R3.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR:Q) (qR:list Sym).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* qR {{QR}}> r) (at level 30).
Definition LC len n := BinDec ld0 ld1 len n ldh.
Hypothesis LInc: forall l r n, l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n, l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv_0: forall r n, ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n <| [0;0;0;1;0] *> r.
Hypothesis LOv_1: forall r n m,
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <| rd0^^m *> [0;0;0] *> rd1 *> r.
Hypothesis ROv2: forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0] *> rd1 *> r.
Hypothesis ROv00: forall l r n m,
  l |> rd1^^n *> rm3 *> rd1^^m *> [0;0] *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0;1;0] *> r.
Hypothesis ROv101: forall l r n m,
  l |> rd1^^n *> [1;0;0;1;0;1] *> [0;0;0;1]^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(2+n*2) <| rd0^^m *> [0;0;0;1] *> r.
Hypothesis ROv10: forall l r n,
  l |> rd1^^n *> [1;0;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n*2) <| r.
Hypothesis ROv33: forall l r n m,
  l |> rd1^^n *> [1;0;0] *> rd1^^m *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(2+n+m) *> [0;0;1] *> r.

Definition RC n := BinInc rd1 n.
Definition RP h n r := BinDec2 [0] [1] [0;0;0] h n r.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX;
  repeat (simpl_rotate || simpl_tape); finish.
Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].

Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc k l: l |> RC k -->+ l <| RC (1+k).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RP_Inc len n r l: 1+n<2^(len+1) -> l |> RP len (1+n) r -->+ l <| RP len n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma RP_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RP h n r -->* LC len k |> RP h 0 r.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc RP_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma Full len k h r: k+2^(h+1)<2^len ->
  LC len (k+2^(h+1)) <| rd0^^h *> [0] *> r -->*
  LC len k |> rd1^^h *> [1] *> r.
Proof.
  intros H.
  change (LC len (k+2^(h+1)) <| ([0]++[0;0;0])^^h *> [0] *> r -->*
    LC len k |> ([1]++[0;0;0])^^h *> [1] *> r).
  rewrite <-(BinDec2_full [0] [1] [0;0;0]), <-(BinDec2_O [0] [1] [0;0;0]); fold RP.
  replace (k+2^(h+1)) with (1+(k+(2^(h+1)-1))) by arith.
  follow_inc LC_Inc.
  follow RP_Incs; try arith; finish.
Qed.

Lemma VInc len k a m: k+2^(a+1)<2^len ->
  LC len (k+2^(a+1)) <| [0;0;0] *> RC ((m*2+1)*2^a) -->*
  LC len k <| [0;0;0] *> RC ((m+1)*2^(a+1)).
Proof.
  intros H; unfold RC.
  rewrite BinInc_mulpow2, BinInc_mul2add1; cbn [BinaryCounter.d0].
  rewrite <-(lpow_rotate' [0] [0;0;0]); cbn [List.app].
  follow Full.
  lowbitS_cases m.
  rewrite BinInc_mulpow2sub1.
  follow_inc ROv2.
  rewrite Nat.sub_add by arith.
  replace (((x*2+1)*2^i)*2^(a+1)) with ((x*2+1)*2^(1+a+i)) by arith.
  rw_Bin; cbn [BinaryCounter.d0]; simpl_rotate; finish.
Qed.
Lemma next_bound h a m:
  (m*2+1)*2^a<2^h -> (m+1)*2^(a+1)<=2^h.
Proof.
  intros H.
  assert (a<h) by (apply Nat.pow_lt_mono_r_iff with (a:=2); nia).
  replace h with (a+1+(h-a-1)) in H |- * by lia.
  repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *.
  assert (m < 2^(h-a-1)) by nia.
  nia.
Qed.

Lemma Sweep len k h v: k+(2^h-v)*2<2^len -> 0<v<=2^h ->
  LC len (k+(2^h-v)*2) <| [0;0;0] *> RC v -->*
  LC len k <| [0;0;0] *> RC (2^h).
Proof.
  remember (2^h-v) as d; gen k v.
  induction d using strong_induction; intros k v E Hk Hv.
  rewrite E in Hk |- *.
  destruct (Nat.eq_dec v (2^h)) as [->|Hne].
  - replace (k+(2^h-2^h)*2) with k by lia; finish.
  - lowbit_cases v; [lia|].
    assert ((x+1)*2^(i+1)<=2^h) by (apply next_bound; lia).
    replace (k+(2^h-(x*2+1)*2^i)*2) with
      ((k+(2^h-(x+1)*2^(i+1))*2)+2^(i+1)) by arith.
    follow VInc; try arith.
    eapply H; try arith.
Qed.
Lemma ZSweep len k a b r: k+2^(a+b+1)-2^(a+1)<2^len ->
  LC len (k+2^(a+b+1)-2^(a+1)) <| rd0^^a *> [0;0;0;1;0] *> rd0^^b *> r -->*
  LC len k <| rd0^^(a+b) *> [0;0;0;1;0] *> r.
Proof.
  gen a k; induction b; intros a k Hk.
  - replace (a+0) with a by lia.
    rewrite Nat.add_sub; finish.
  - replace (k+2^(a+S b+1)-2^(a+1)) with
      ((k+2^((a+1)+b+1)-2^((a+1)+1))+2^(a+1)) by arith.
    rewrite lpow_S.
    follow Full; [arith|].
    epose proof (ROv00 _ _ a 0) as HX; cbn [lpow] in HX; follow_inc HX.
    replace (1+a+0) with (a+1) by lia.
    follow IHb; try arith; applys_eq evstep_refl; flia.
Qed.
Lemma Tail101 len k a m: k<2^len ->
  LC len k |> rd1^^a *> [1;0;0;1;0;1;0;0;0] *> RC m -->+
  LC (len+1+(2+a*2)) ((k*2+1)*2^(2+a*2)-1) <| [0;0;0] *> RC (m+1).
Proof.
  intros H; lowbitS_cases m; unfold RC, LC.
  rewrite BinInc_mulpow2sub1.
  match goal with |- _ -->+ ?t =>
    change (BinDec ld0 ld1 len k ldh |> rd1^^a *> [1;0;0;1;0;1] *>
      [0;0;0] *> rd1^^i *> rd0 *> BinInc rd1 x -->+ t)
  end.
  replace ([0;0;0] *> rd1^^i *> rd0 *> BinInc rd1 x) with
    ([0;0;0;1]^^i *> [0;0;0] *> rd0 *> BinInc rd1 x)
    by exact (lpow_rotate' [1] [0;0;0] (rd0 *> BinInc rd1 x) i).
  follow10 ROv101.
  rewrite Nat.sub_add by arith.
  rewrite BinInc_mulpow2, BinInc_mul2add1; cbn [BinaryCounter.d0].
  rewrite BinDec_mulpow2sub1' by arith.
  replace (k*2+1-1) with (k*2) by lia.
  rewrite BinDec_mul2 by arith; simpl_rotate; finish.
Qed.
Lemma StageA len a m: a+2<=len ->
  LC len 0 <| RC ((m*2+1)*2^(a+1)) -->+
  LC (len+1+(2+a*2)) (((2^len-2^(a+2)+1)*2+1)*2^(2+a*2)-1) <|
    [0;0;0] *> RC (m+1).
Proof.
  intros H; assert (2^(a+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  unfold LC, RC; rewrite BinDec_O, BinInc_mulpow2, BinInc_mul2add1.
  cbn [BinaryCounter.d0]; fold LC; fold RC.
  replace (a+1) with (S a) by lia; rewrite lpow_S.
  follow10 LOv_0.
  replace (ldh <* ld0^^len) with (LC len (2^len-1)) by (unfold LC; apply BinDec_full).
  fold RC.
  replace (2^len-1) with ((2^len-2^(a+1)+1)+2^(0+a+1)-2^(0+1)) by arith.
  follow ZSweep; [arith|].
  replace (0+a) with a by lia.
  replace (2^len-2^(a+1)+1) with ((2^len-2^(a+2)+1)+2^(a+1)) by arith.
  follow Full; [arith|].
  fold RC; apply progress_evstep, Tail101; arith.
Qed.

Lemma Increments len k n m: k+n<2^len ->
  LC len (k+n) <| RC m -->* LC len k <| RC (m+n).
Proof.
  gen k m; induction n; intros k m H; [rewrite !Nat.add_0_r; finish|].
  rewrite Nat.add_succ_r; follow_inc LC_Inc; follow_inc RC_Inc.
  follow IHn; try lia; applys_eq evstep_refl; flia.
Qed.
Lemma CarryFinish len k a b: k+2^(a+1)<2^len ->
  LC len (k+2^(a+1)) <| rd0^^a *> [0;0;0;1] *> [0;0;0;1]^^b *> [0;0;1] *> 0inf -->*
  LC len k <| rd0^^(2+a+b) *> [0;0;1] *> 0inf.
Proof.
  intros H; follow Full.
  match goal with |- _ -->* ?t =>
    change (LC len k |> rd1^^a *> [1;0;0] *> [1] *>
      [0;0;0;1]^^b *> [0;0;1] *> 0inf -->* t)
  end.
  replace ([1] *> [0;0;0;1]^^b *> [0;0;1] *> 0inf) with
    (rd1^^b *> [1;0;0;1] *> 0inf)
    by exact (lpow_rotate' [0;0;0] [1] ([0;0;1] *> 0inf) b).
  epose proof (ROv33 _ 0inf a b) as HX.
  cbn [Str_app] in HX; repeat rewrite <-(const_unfold _ 0) in HX.
  follow_inc HX; finish.
Qed.
Definition SF h n := BinDec [0;0;0;1] rd0 h n ([0;0;0;1;0;0;1] *> 0inf).
Lemma SF_head h n: n<2^h -> exists r, SF h n = [0;0;0] *> r.
Proof.
  intros H; unfold SF; destruct h as [|h].
  - assert (n=O) by (cbn [Nat.pow] in H; lia); subst; rewrite BinDec_O; eexists; reflexivity.
  - replace (S h) with (h+1) by lia.
    destruct (Nat.Even_or_Odd n) as [[m E]|[m E]].
    + replace n with (m*2) by lia; rewrite BinDec_mul2 by arith; eexists; reflexivity.
    + replace n with (m*2+1) by lia; rewrite BinDec_mul2add1 by arith; eexists; reflexivity.
Qed.
Lemma FCarry len k a b h x: x<2^h -> k+2^(a+1)<2^len ->
  LC len (k+2^(a+1)) <| SF (h+1+b+1+a) ((((x*2+1)*2^b-1)*2+1)*2^a) -->*
  LC len k <| SF (h+1+b+1+a) ((x*2+1)*2^(a+b+1)).
Proof.
  intros Hx Hk; unfold SF.
  assert ((x*2+1)*2^b<2^(h+1+b)) by solve_pow2_lt.
  rewrite (BinDec_mulpow2 _ _ (h+1+b+1) _ a) by solve_pow2_lt.
  rewrite BinDec_mul2add1 by solve_pow2_lt.
  rewrite BinDec_mulpow2sub1 by lia.
  destruct (SF_head h x Hx) as [r E]; unfold SF in E; rewrite E.
  follow Full.
  match goal with |- _ -->* ?t =>
    change (LC len k |> rd1^^a *> [1;0;0] *> [1] *>
      [0;0;0;1]^^b *> rd0 *> [0;0;0] *> r -->* t)
  end.
  replace ([1] *> [0;0;0;1]^^b *> rd0 *> [0;0;0] *> r) with
    (rd1^^b *> [1] *> rd0 *> [0;0;0] *> r)
    by exact (lpow_rotate' [0;0;0] [1] (rd0 *> [0;0;0] *> r) b).
  match goal with |- _ -->* ?t =>
    change (LC len k |> rd1^^a *> [1;0;0] *> (rd1^^b *> rd1 *> rd0 *> r) -->* t)
  end.
  replace (rd1^^b *> rd1 *> rd0 *> r) with (rd1 *> rd1^^b *> rd0 *> r)
    by (symmetry; exact (lpow_rotate' [] rd1 (rd0 *> r) b)).
  follow_inc ROv2.
  replace (h+1+b+1+a) with (h+1+(a+b+1)) by lia.
  rewrite BinDec_mulpow2 by solve_pow2_lt; rewrite BinDec_mul2add1 by solve_pow2_lt.
  rewrite E; applys_eq evstep_refl; flia.
Qed.
Lemma FFinish len k a b: k+2^(a+1)<2^len ->
  LC len (k+2^(a+1)) <| SF (b+a) ((2^b-1)*2^a) -->*
  LC len k <| rd0^^(b+a+2) *> [0;0;1] *> 0inf.
Proof.
  intros H; unfold SF.
  rewrite BinDec_mulpow2 by solve_pow2_lt; rewrite BinDec_full.
  match goal with |- _ -->* ?t =>
    change (LC len (k+2^(a+1)) <| rd0^^a *>
      ([0;0;0;1]^^b *> [0;0;0;1;0;0;1] *> 0inf) -->* t)
  end.
  replace ([0;0;0;1]^^b *> [0;0;0;1;0;0;1] *> 0inf) with
    ([0;0;0;1] *> [0;0;0;1]^^b *> [0;0;1] *> 0inf)
    by (symmetry; exact (lpow_rotate' [] [0;0;0;1] ([0;0;1] *> 0inf) b)).
  follow CarryFinish; applys_eq evstep_refl; flia.
Qed.
Lemma FSweep len k h n: n<2^h -> k+(2^h-n)*2<2^len ->
  LC len (k+(2^h-n)*2) <| SF h n -->*
  LC len k <| rd0^^(h+2) *> [0;0;1] *> 0inf.
Proof.
  remember (2^h-n) as d; gen k n.
  induction d using strong_induction; intros k n E Hn Hk.
  rewrite E in Hk |- *.
  lowbit_cases n.
  - applys_eq (FFinish len k h O); repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; flia.
  - pose proof (lowbit_split _ _ _ Hn) as Hw.
    pose proof (lowbit_split_lt _ _ _ Hn) as Hx.
    remember (h-i-1) as q in *.
    destruct (Nat.eq_dec x (2^q-1)) as [->|Hne].
    + replace (k+(2^h-((2^q-1)*2+1)*2^i)*2) with (k+2^(i+1))
        by (rewrite Hw; arith).
      replace ((2^q-1)*2+1) with (2^(q+1)-1) by arith.
      rewrite Hw; apply FFinish; rewrite Hw in Hk; arith.
    + destruct (lowbitS_cases' x) as [y b].
      assert (Hy: (y*2+1)*2^b<2^q) by lia.
      pose proof (lowbit_split _ _ _ Hy) as Hq.
      pose proof (lowbit_split_lt _ _ _ Hy) as Hy'.
      remember (q-b-1) as j in *.
      assert (Hnext: (y*2+1)*2^(i+b+1)<2^h).
      { rewrite Hw,Hq; replace (j+1+b+1+i) with (j+1+(i+b+1)) by lia; solve_pow2_lt. }
      replace (k+(2^h-(((y*2+1)*2^b-1)*2+1)*2^i)*2) with
        ((k+(2^h-(y*2+1)*2^(i+b+1))*2)+2^(i+1)) by arith.
      rewrite Hw,Hq.
      follow FCarry; [rewrite <-Hq,<-Hw; arith|].
      rewrite <-Hq,<-Hw.
      eapply H; try arith.
Qed.
Lemma BinDec_extend d0 d1 h n r: n<2^h ->
  BinDec d0 d1 (h+1) n r = BinDec d0 d1 h n (d1 *> r).
Proof.
  gen n; induction h; intros n H.
  - assert (n=O) by (cbn [Nat.pow] in H; lia); subst; rewrite !BinDec_O; cbn [lpow]; simpl_tape; reflexivity.
  - replace (S h) with (h+1) in * by lia.
    destruct (Nat.Even_or_Odd n) as [[m E]|[m E]].
    + replace n with (m*2) in * by lia; rewrite !BinDec_mul2 by arith.
      rewrite IHh by arith; reflexivity.
    + replace n with (m*2+1) in * by lia; rewrite !BinDec_mul2add1 by arith.
      rewrite IHh by arith; reflexivity.
Qed.
Lemma BinDec_complement d0 d1 h n r: n<2^h ->
  BinDec d0 d1 h n r = BinDec d1 d0 h (2^h-1-n) r.
Proof.
  gen n; induction h; intros n H.
  - assert (n=O) by (cbn [Nat.pow] in H; lia); subst; rewrite !BinDec_O; reflexivity.
  - replace (S h) with (h+1) in * by lia.
    destruct (Nat.Even_or_Odd n) as [[m E]|[m E]].
    + replace n with (m*2) in * by lia.
      replace (2^(h+1)-1-m*2) with ((2^h-1-m)*2+1) by arith.
      rewrite BinDec_mul2 by arith; rewrite BinDec_mul2add1 by arith.
      rewrite IHh by arith; reflexivity.
    + replace n with (m*2+1) in * by lia.
      replace (2^(h+1)-1-(m*2+1)) with ((2^h-1-m)*2) by arith.
      rewrite BinDec_mul2add1 by arith; rewrite BinDec_mul2 by arith.
      rewrite IHh by arith; reflexivity.
Qed.
Lemma RP_Consume len k h n r: k<2^len -> n+k<2^(h+1) ->
  LC len k <| RP h (n+k) r -->* LC len 0 <| RP h n r.
Proof.
  induction k; intros Hk Hn; [rewrite Nat.add_0_r; finish|].
  follow_inc LC_Inc; rewrite Nat.add_succ_r; follow_inc RP_Inc.
  follow IHk; try lia; finish.
Qed.
Lemma Partial len k h r: k<2^len -> k<2^(h+1) ->
  LC len k <| rd0^^h *> [0] *> r -->*
  LC len 0 <| RP h (2^(h+1)-1-k) r.
Proof.
  intros Hk Hn.
  change (LC len k <| ([0]++[0;0;0])^^h *> [0] *> r -->*
    LC len 0 <| RP h (2^(h+1)-1-k) r).
  rewrite <-(BinDec2_full [0] [1] [0;0;0]); fold RP.
  replace (2^(h+1)-1) with ((2^(h+1)-1-k)+k) at 1 by lia.
  apply RP_Consume; lia.
Qed.
Lemma BinDec_prefix h n r: n<2^(h+1) ->
  exists s, BinDec rd0 [0;0;0;1] (h+1) n r = [0;0;0] *> s.
Proof.
  intros H; destruct (Nat.Even_or_Odd n) as [[m E]|[m E]].
  - replace n with (m*2) by lia; rewrite BinDec_mul2 by arith; eexists; reflexivity.
  - replace n with (m*2+1) by lia; rewrite BinDec_mul2add1 by arith; eexists; reflexivity.
Qed.
Lemma SF_alt h m: 0<m<=2^h ->
  SF h (2^h-m) = BinDec rd0 [0;0;0;1] h (m-1) ([0;0;0;1;0;0;1] *> 0inf).
Proof. intros; unfold SF; rewrite BinDec_complement by lia; f_equal; lia. Qed.
Lemma Reset len h m: 0<m<2^h ->
  LC len 0 <| RP (h+1) (m*2) ([0;0;1] *> 0inf) -->+
  LC (len+1) ((2^len-1)*2) <| SF h (2^h-m).
Proof.
  intros H; lowbit_cases m; [lia|].
  assert (Hw: h=h-i-1+1+i) by (apply lowbit_split with (m:=x); lia).
  assert (Hx: x<2^(h-i-1)) by (apply lowbit_split_lt with (i:=i); lia).
  remember (h-i-1) as q in *.
  rewrite SF_alt by lia; unfold LC, RP; rewrite BinDec_O.
  rewrite Hw; replace (q+1+i+1) with (q+1+(i+1)) by lia.
  replace ((x*2+1)*2^i*2) with ((x*2+1)*2^(i+1)) by arith.
  rewrite BinDec2_mulpow2 by solve_pow2_lt; cbn [List.app].
  destruct (BinDec_prefix q x ([0;0;1] *> 0inf) ltac:(arith)) as [r E].
  cbn [Str_app] in E |- *.
  unfold Sym in *.
  rewrite E; replace (i+1) with (1+i) by lia.
  follow10 LOv_1.
  rewrite BinDec_extend in E by lia.
  rewrite BinDec_mulpow2sub1 by solve_pow2_lt; cbn [Str_app] in E |- *; unfold Sym in *; rewrite E.
  rewrite BinDec_mul2 by arith; rewrite BinDec_full; finish.
Qed.
Lemma Power_right a: [0;0;0] *> RC (2^a) = rd0^^a *> [0;0;0;1] *> 0inf.
Proof.
  replace (2^a) with ((0*2+1)*2^a) by lia; unfold RC; rw_Bin; cbn [BinaryCounter.d0].
  simpl_rotate; simpl_tape; reflexivity.
Qed.
Lemma Tail10 len k a: k<2^len ->
  LC len k |> rd1^^a *> [1;0;1] *> 0inf -->+
  LC (len+1+(1+a*2)) ((k*2+1)*2^(1+a*2)) <| 0inf.
Proof.
  intros H; unfold LC.
  epose proof (ROv10 _ 0inf a) as HX.
  cbn [Str_app] in HX; repeat rewrite <-(const_unfold _ 0) in HX.
  follow10 HX.
  rewrite BinDec_mulpow2 by solve_pow2_lt; rewrite BinDec_mul2add1 by solve_pow2_lt; finish.
  cbn [Str_app]; repeat rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Lemma StageB h m: 0<m<2^h ->
  LC (h+3) (2^(h+2)-1-m*2) <| [0;0;0] *> RC (2^(h+1)) -->*
  LC (h*3+10) ((2^(h+4)-3-m*4)*2^(h*2+5)) <| 0inf.
Proof.
  intros H; rewrite Power_right.
  follow Partial; [arith|arith|].
  replace (2^(h+1+1)-1-(2^(h+2)-1-m*2)) with (m*2) by arith.
  follow_inc Reset.
  replace ((2^(h+3)-1)*2) with
    (((2^(h+3)-1)*2-m*2)+(2^h-(2^h-m))*2) by arith.
  follow FSweep; [lia|arith|].
  replace ((2^(h+3)-1)*2-m*2) with
    ((2^(h+3)-2-m*2)+2^(h+2+1)) by arith.
  follow Full; [arith|].
  eapply evstep_trans; [apply progress_evstep, Tail10; arith|].
  replace (1+(h+2)*2) with (h*2+5) by lia.
  replace ((2^(h+3)-2-m*2)*2+1) with (2^(h+4)-3-m*4) by arith.
  applys_eq evstep_refl; flia.
Qed.

Definition Valid len a m := 1<=a /\ a+4<=len<=a*3+4 /\ m<2^(len-a-2).
Definition gap a m := (2^(a+3)-3)*2^(a*2+1)-m-1.
Lemma gap_bounds len a m: Valid len a m -> 0<gap a m<2^(len+a*2).
Proof.
  intros [Ha [HL Hm]]; unfold gap.
  assert (Hm': m<2^(a*2+2)).
  { eapply Nat.lt_le_trans; [apply Hm|apply Nat.pow_le_mono_r; lia]. }
  assert (Ha': 16<=2^(a+3)) by (change (2^4<=2^(a+3)); apply Nat.pow_le_mono_r; lia).
  assert (Hp: 2^(a+3+(a*2+1))<=2^(len+a*2)) by (apply Nat.pow_le_mono_r; lia).
  arith.
Qed.
Lemma valid_capacity len a m: Valid len a m -> (m*2+1)*2^(a+1)<2^len.
Proof.
  intros [Ha [HL Hm]].
  replace len with (len-a-2+1+(a+1)) by lia; solve_pow2_lt.
Qed.
Lemma Start len n: n<2^len -> LC len n <| 0inf -->* LC len 0 <| RC n.
Proof.
  intros H; epose proof (Increments len O n O) as HX.
  cbn [Nat.add] in HX; unfold RC in HX; rewrite BinInc_O in HX; apply HX,H.
Qed.
Definition cfg len a m := LC len ((m*2+1)*2^(a+1)) <| 0inf.
Lemma cycle len a m: Valid len a m ->
  cfg len a m -->+
  cfg ((len+a*2)*3+10) ((len+a*2)*2+4) (2^(len+a*2+3)-2-gap a m*2).
Proof.
  intros HV; pose proof (gap_bounds _ _ _ HV) as HG.
  pose proof (valid_capacity _ _ _ HV) as HC.
  destruct HV as [Ha [HL Hm]].
  remember (len+a*2) as h eqn:Eh in *.
  assert (Hm': m+1<=2^(h+1)).
  { transitivity (2^(len-a-2)); [lia|apply Nat.pow_le_mono_r; lia]. }
  assert (Ht: 2^len-2^(a+2)+1<2^len).
  { assert (2^(a+2)<=2^len) by (apply Nat.pow_le_mono_r; lia); arith. }
  assert (HK: ((2^len-2^(a+2)+1)*2+1)*2^(2+a*2)-1<2^(h+3)).
  { replace (h+3) with (len+1+(2+a*2)) by lia; solve_pow2_lt. }
  unfold cfg.
  mid01 (LC len 0 <| RC ((m*2+1)*2^(a+1))); [apply Start,HC|].
  eapply progress_evstep_trans; [apply StageA; lia|].
  replace (len+1+(2+a*2)) with (h+3) by lia.
  assert (EB: ((2^len-2^(a+2)+1)*2+1)*2^(2+a*2)-1 =
    (2^(h+2)-1-gap a m*2)+(2^(h+1)-(m+1))*2).
  { assert (HP: 2^(a+2)<=2^len) by (apply Nat.pow_le_mono_r; lia).
    clear -HG Hm' HP Eh; unfold gap in *; subst h; arith. }
  rewrite EB in HK |- *.
  follow Sweep; [lia|].
  follow StageB.
  replace (h*2+4+1) with (h*2+5) by lia.
  replace ((2^(h+3)-2-gap a m*2)*2+1) with (2^(h+4)-3-gap a m*4) by (clear -HG; arith).
  finish.
Qed.
Lemma Valid_next h g: Valid (h*3+10) (h*2+4) (2^(h+3)-2-g*2).
Proof.
  unfold Valid; repeat split; try lia.
  replace (h*3+10-(h*2+4)-2) with (h+4) by lia; arith.
Qed.
Lemma cfg_nonhalt len a m: Valid len a m -> ~halts tm (cfg len a m).
Proof.
  intros HP.
  apply (progress_nonhalt_cond tm (nat*nat*nat) (len,a,m)
    (fun '(len,a,m)=>cfg len a m) (fun '(len,a,m)=>Valid len a m)).
  - intros [[L a0] m0] H.
    eexists (_,_,_); split; [apply cycle,H|apply Valid_next].
  - exact HP.
Qed.
End Counter.
End Counter.
End SOC24_R3.

(* SOC24_R3.TM245 *)
Module TM245.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC24_R3.

Definition tm := Eval compute in (TM_from_str "1LB0RB_0LC---_1LD0LC_1RE1LD_0RA1RF_1RD0RE").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Notation "l <| r" := (l <{{D}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [0;0;1] {{A}}> r) (at level 30).

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n: ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n <| [0;0;0;1;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <| rd0^^m *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.

Lemma ROv00 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> [0;0] *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0;1;0] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv101 l r n m:
  l |> rd1^^n *> [1;0;0;1;0;1] *> [0;0;0;1]^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(2+n*2) <| rd0^^m *> [0;0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv10 l r n:
  l |> rd1^^n *> [1;0;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n*2) <| r.
Proof. es' n & l r. Qed.
Lemma ROv33 l r n m:
  l |> rd1^^n *> [1;0;0] *> rd1^^m *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(2+n+m) *> [0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma init: c0 -[ tm ]->* (LC 5 20 <| 0inf).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (Counter.cfg D 5 1 2)).
  eapply Counter.cfg_nonhalt with (QR:=A) (qR:=[0;0;1]);
    try solve [apply LInc|apply RInc|apply LOv_0|apply LOv_1|apply ROv2|
      apply ROv00|apply ROv101|apply ROv10|apply ROv33].
    unfold Counter.Valid; cbn; lia.
Qed.
End TM245.

(* SOC24_R3.TM250 *)
Module TM250.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC24_R3.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC1RF_1LD0LC_1RA1LD_1RD0RA_0LA---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Notation "l <| r" := (l <{{D}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1] {{B}}> r) (at level 30).

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n: ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n <| [0;0;0;1;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <| rd0^^m *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.

Lemma ROv00 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> [0;0] *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0;1;0] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv101 l r n m:
  l |> rd1^^n *> [1;0;0;1;0;1] *> [0;0;0;1]^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(2+n*2) <| rd0^^m *> [0;0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv10 l r n:
  l |> rd1^^n *> [1;0;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n*2) <| r.
Proof. es' n & l r. Qed.
Lemma ROv33 l r n m:
  l |> rd1^^n *> [1;0;0] *> rd1^^m *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(2+n+m) *> [0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma init: c0 -[ tm ]->* (LC 5 20 <| 0inf).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (Counter.cfg D 5 1 2)).
  eapply Counter.cfg_nonhalt with (QR:=B) (qR:=[1;0;1]);
    try solve [apply LInc|apply RInc|apply LOv_0|apply LOv_1|apply ROv2|
      apply ROv00|apply ROv101|apply ROv10|apply ROv33].
    unfold Counter.Valid; cbn; lia.
Qed.
End TM250.

(* SOC24_R3.TM253 *)
Module TM253.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.

Import SOC24_R3.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1LC0LB_1RD1LC_1RA1RE_0LA0RD_1RC---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].
Definition LC len n := BinDec ld0 ld1 len n ldh.
Notation "l <| r" := (l <{{C}} [1;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1] {{A}}> r) (at level 30).

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv_0 r n: ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n <| [0;0;0;1;0] *> r.
Proof. es. Qed.
Lemma LOv_1 r n m:
  ldh <* ld1^^n <| rd1^^(1+m) *> rd0 *> r -->+
  ldh <* ld0^^n <* ld1 <| rd0^^m *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.
Lemma ROv2 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> rd0 *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0] *> rd1 *> r.
Proof. es. Qed.

Lemma ROv00 l r n m:
  l |> rd1^^n *> rm3 *> rd1^^m *> [0;0] *> r -->+
  l <| rd0^^(1+n+m) *> [0;0;0;1;0] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv101 l r n m:
  l |> rd1^^n *> [1;0;0;1;0;1] *> [0;0;0;1]^^m *> rd0 *> r -->+
  l <* ld1 <* ld0^^(2+n*2) <| rd0^^m *> [0;0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma ROv10 l r n:
  l |> rd1^^n *> [1;0;1;0] *> r -->+
  l <* ld0 <* ld1^^(1+n*2) <| r.
Proof. es' n & l r. Qed.
Lemma ROv33 l r n m:
  l |> rd1^^n *> [1;0;0] *> rd1^^m *> [1;0;0;1;0;0;0;0] *> r -->+
  l <| rd0^^(2+n+m) *> [0;0;1] *> r.
Proof. es' n m & l r. Qed.
Lemma init: c0 -[ tm ]->* (ldh <* ld0^^2 <* ld1^^2 <* ld0 <* ld1^^2 <* ld0 <* ld1 <* ld0^^2 <* ld1^^5 <| 0inf).
Proof. esx. Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=Counter.cfg C 16 4 805).
  - eapply evstep_trans; [apply init|].
    unfold Counter.cfg, Counter.LC; vm_compute; apply evstep_refl.
  - eapply Counter.cfg_nonhalt with (QR:=A) (qR:=[1;0;1]);
    try solve [apply LInc|apply RInc|apply LOv_0|apply LOv_1|apply ROv2|
      apply ROv00|apply ROv101|apply ROv10|apply ROv33].
    unfold Counter.Valid; cbn; lia.
Qed.
End TM253.

From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2 ES_v3.
Require Import ZifyNat Lia PeanoNat String.

(* SOC24_TM166.TM166 *)
Module TM166.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2 BusyCoq.ES_v3.
Import ZifyNat Lia PeanoNat String.


Definition tm := Eval compute in (TM_from_str "1LB1RD_1LC0LB_1RA0RE_1RF0RA_0RD1LB_1RC---").
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation ld0 := <[1;0].
Notation ld1 := <[1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0;0].
Notation rd1 := [1;0;0;0].
Notation rm1 := [1;1;0;0;0].
Notation rm3 := [1;0;0;1;0;0;0].
Notation cd0 := <[0;0;1;1].
Notation cd1 := <[1;1;1;1].
Notation "l <| r" := (l <{{C}} [1;1] *> r) (at level 30).
Notation "l |> r" := (l <* [0;1] {{A}}> r) (at level 30).
Definition LC len n := BinDec ld0 ld1 len n ldh.

Lemma LInc l r n: l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.
Lemma RInc l r n: l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Proof. es. Qed.
Lemma LOv r n: ldh <* ld1^^n <| r -->+ ldh <* ld0^^n |> [1] *> r.
Proof. es. Qed.
Lemma ROv1 l r n:
  l |> rd1^^n *> rm1 *> r -->+ l <* ld1 <* ld0^^(n*2) |> [1;0;0] *> r.
Proof. es. Qed.

Lemma CoreEnter l r n: l |> rd1^^n *> rm3 *> r -->+
  l <* [0;1] <* cd1^^n <* [1;1;1] <* cd0 {{C}}> r.
Proof. es' n & l r. Qed.
Lemma CoreD l r: l {{C}}> rd1 *> r -->+ l <* cd0 {{C}}> r.
Proof. es' & l r. Qed.
Lemma CoreT l r: l {{C}}> [0;1;0;0] *> r -->+ l <* cd1 {{C}}> r.
Proof. es' & l r. Qed.
Lemma CoreZ l r n: l <* cd0 <* cd1^^n {{C}}> rd0 *> r -->+
  l <* cd1 {{C}}> rd0^^n *> [0;1;0;0] *> r.
Proof. es' n & l r. Qed.
Lemma CoreExit l r n: l <* [0;1] <* cd1^^n <* [1;1;1] {{C}}> rd0 *> r -->+
  l <| rd0^^(n+1) *> [1;0;0] *> r.
Proof. es' n & l r. Qed.
Lemma init: c0 -[ tm ]->* (LC 4 10 <| rd1 *> 0inf).
Proof. esx. Qed.

Definition RC n := BinInc rd1 n.
Notation td := [0;1;0;0].
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.

(* n is the virtual value, w the weight of the unconsumed shifted tail. *)
Inductive Num: nat -> nat -> side -> Prop :=
| NumOrd n: Num n 0 (RC n)
| NumShort0 m: Num (m*6) m ([0;0;0] *> RC m)
| NumShort1 m: Num (m*6+1) m ([1;0;0] *> RC m)
| NumZ n w r: Num n w r -> Num (n*2) (w*2) (rd0 *> r)
| NumD n w r: Num n w r -> Num (n*2+1) (w*2) (rd1 *> r).

Lemma Num_bound n w r: Num n w r -> 0<w -> n<w*8.
Proof. induction 1; intros; lia. Qed.
Lemma Num_ordinary n w r: Num n w r -> w=0%nat -> r=RC n.
Proof.
  induction 1; intros Hw.
  - reflexivity.
  - subst m; unfold RC; rewrite BinInc_O; cbn [Str_app];
      repeat rewrite <-(const_unfold _ 0); reflexivity.
  - subst m; unfold RC; rewrite BinInc_O.
    change ([1;0;0] *> 0inf = BinInc rd1 (0*2+1)).
    rewrite BinInc_mul2add1, BinInc_O; unfold Sym; cbn [Str_app];
      repeat rewrite <-(const_unfold _ 0); reflexivity.
  - rewrite IHNum by lia; unfold RC; rewrite BinInc_mul2; reflexivity.
  - rewrite IHNum by lia; unfold RC; rewrite BinInc_mul2add1; reflexivity.
Qed.
Lemma Num_zeros n w r a: Num n w r -> Num (n*2^a) (w*2^a) (rd0^^a *> r).
Proof.
  intros H; induction a; cbn [lpow].
  - applys_eq H; flia.
  - rewrite Nat.pow_succ_r'.
    applys_eq (NumZ _ _ _ IHa); flia.
Qed.

(* Generated Z/T prefix, followed by the untouched ordinary input. *)
Inductive Input: nat -> nat -> side -> Prop :=
| InputEnd m: Input (m*6) m (RC m)
| InputZ v w r: Input v w r -> Input (v*2) (w*2) (rd0 *> r)
| InputT v w r: Input v w r -> Input (v*2+2) (w*2) (td *> r).

Lemma Input_zeros v w r a: Input v w r -> Input (v*2^a) (w*2^a) (rd0^^a *> r).
Proof.
  intros H; induction a; cbn [lpow].
  - applys_eq H; flia.
  - rewrite Nat.pow_succ_r'.
    applys_eq (InputZ _ _ _ IHa); flia.
Qed.
Lemma Input_Num v w r: Input v w r ->
  Num v w ([0;0;0] *> r) /\ Num (v+1) w ([1;0;0] *> r).
Proof.
  induction 1 as [m|v w r H [H0 H1]|v w r H [H0 H1]]; split.
  - apply NumShort0.
  - apply NumShort1.
  - change (Num (v*2) (w*2) (rd0 *> [0;0;0] *> r)); apply NumZ,H0.
  - change (Num (v*2+1) (w*2) (rd1 *> [0;0;0] *> r)); apply NumD,H0.
  - change (Num (v*2+2) (w*2) (rd0 *> [1;0;0] *> r)).
    applys_eq (NumZ _ _ _ H1); flia.
  - change (Num (v*2+2+1) (w*2) (rd1 *> [1;0;0] *> r)).
    applys_eq (NumD _ _ _ H1); flia.
Qed.

Lemma Input_cases v w r: Input v w r ->
  (exists v' w' r', Input v' w' r' /\ r=rd0 *> r' /\ v=v'*2 /\ w=w'*2) \/
  (exists v' w' r', Input v' w' r' /\ r=td *> r' /\ v=v'*2+2 /\ w=w'*2) \/
  (exists v' w' r', Input v' w' r' /\ r=rd1 *> r' /\ v=v'*2+6 /\ w=w'*2+1).
Proof.
  destruct 1.
  - divmod2_cases m; unfold RC; rw_Bin; cbn [BinaryCounter.d0].
    + left; exists (n'*6),n',(RC n'); repeat split; try apply InputEnd; try reflexivity; lia.
    + right; right; exists (n'*6),n',(RC n'); repeat split; try apply InputEnd; try reflexivity; lia.
  - left; eauto 8.
  - right; left; eauto 8.
Qed.

(* q counts words; z is the binary weight of the 0011 words. *)
Inductive Stack (base:side): nat -> nat -> side -> Prop :=
| StackNil: Stack base 0 0 base
| StackD q z l: Stack base q z l -> Stack base (q+1) (z+2^q) (l <* cd0)
| StackT q z l: Stack base q z l -> Stack base (q+1) z (l <* cd1).

Lemma Stack_cases base q z l: Stack base q z l ->
  (z=0%nat /\ l=base <* cd1^^q) \/
  (exists q' z' l' j, Stack base q' z' l' /\ q=q'+1+j /\ z=z'+2^q' /\
    l=l' <* cd0 <* cd1^^j).
Proof.
  induction 1 as [|q z l H IH|q z l H IH].
  - left; split; reflexivity.
  - right; exists q,z,l,0%nat; repeat split; auto; lia.
  - destruct IH as [[-> ->]|[q' [z' [l' [j [HS [-> [-> ->]]]]]]]].
    + left; split; [reflexivity|]; rewrite Nat.add_1_r, lpow_S; reflexivity.
    + right; exists q',z',l',(j+1); repeat split; auto; try lia.
      rewrite Nat.add_1_r, lpow_S; reflexivity.
Qed.

Definition CV h q z v := (v+2)*2^(h+q)+z*4*2^h.
Definition CW h q z w := z*2^h+w*2^(h+q).
Definition rank f u p := f*(u+1)-p.
Definition measure h q z v w := rank (CV h q z v) (CW h q z w) (2^(h+q)).

Lemma rank_forward f u p: 0<p -> p*2<=f -> rank f u (p*2)<rank f u p.
Proof. unfold rank; nia. Qed.
Lemma rank_backward f u u' p p': u'<u -> 0<p' -> p<=f -> p'<=f ->
  rank f u' p'<rank f u p.
Proof. unfold rank; nia. Qed.
Lemma CV_bound h q z v: 2^(h+q)<=CV h q z v.
Proof. unfold CV; nia. Qed.
Lemma CV_D h q z v: CV h (q+1) (z+2^q) v = CV h q z (v*2+6).
Proof. unfold CV; arith. Qed.
Lemma CW_D h q z w: CW h (q+1) (z+2^q) w = CW h q z (w*2+1).
Proof. unfold CW; arith. Qed.
Lemma CV_T h q z v: CV h (q+1) z v = CV h q z (v*2+2).
Proof. unfold CV; arith. Qed.
Lemma CW_T h q z w: CW h (q+1) z w = CW h q z (w*2).
Proof. unfold CW; arith. Qed.
Lemma CV_Z h q z j v:
  CV h (q+1) z ((v*2+2)*2^j) = CV h (q+1+j) (z+2^q) (v*2).
Proof. unfold CV; arith. Qed.
Lemma CW_Z h q z j w:
  CW h (q+1) z (w*2*2^j)+2^(h+q) = CW h (q+1+j) (z+2^q) (w*2).
Proof. unfold CW; arith. Qed.

Lemma measure_D h q z v w:
  measure h (q+1) (z+2^q) v w < measure h q z (v*2+6) (w*2+1).
Proof.
  unfold measure; rewrite CV_D,CW_D.
  replace (2^(h+(q+1))) with (2^(h+q)*2) by arith.
  apply rank_forward; unfold CV; arith.
Qed.
Lemma measure_T h q z v w:
  measure h (q+1) z v w < measure h q z (v*2+2) (w*2).
Proof.
  unfold measure; rewrite CV_T,CW_T.
  replace (2^(h+(q+1))) with (2^(h+q)*2) by arith.
  apply rank_forward; unfold CV; arith.
Qed.
Lemma measure_Z h q z j v w:
  measure h (q+1) z ((v*2+2)*2^j) (w*2*2^j) <
  measure h (q+1+j) (z+2^q) (v*2) (w*2).
Proof.
  unfold measure; rewrite CV_Z.
  apply rank_backward.
  - rewrite <-CW_Z; arith.
  - arith.
  - apply CV_bound.
  - rewrite <-CV_Z; apply CV_bound.
Qed.

Lemma CoreExit_split l r h q:
  l <* [0;1] <* cd1^^h <* [1;1;1] <* cd1^^q {{C}}> rd0 *> r -->+
  l <| rd0^^(h+q+1) *> [1;0;0] *> r.
Proof. es' h q & l r. Qed.

Lemma CoreReturn l h q z s v w r:
  Stack (l <* [0;1] <* cd1^^h <* [1;1;1]) q z s -> Input v w r ->
  exists w' r', Num (CV h q z v) w' r' /\ w'<=w*2^(h+q) /\
    s {{C}}> r -->* l <| r'.
Proof.
  remember (measure h q z v w) as t eqn:E; gen q z s v w r.
  induction t using strong_induction; intros q z s v w E r HS HI.
  destruct (Input_cases _ _ _ HI) as
    [[v' [w' [r' [HR [-> [-> ->]]]]]]|
    [[v' [w' [r' [HR [-> [-> ->]]]]]]|[v' [w' [r' [HR [-> [-> ->]]]]]]]].
  - destruct (Stack_cases _ _ _ _ HS) as [[-> ->]|[q' [z' [s' [j [HL [-> [-> ->]]]]]]]].
    + exists (w'*2^(h+q+1)),(rd0^^(h+q+1) *> [1;0;0] *> r'); repeat split.
      * replace (CV h q 0 (v'*2)) with ((v'+1)*2^(h+q+1)) by (unfold CV; arith).
        apply Num_zeros, (proj2 (Input_Num _ _ _ HR)).
      * arith.
      * apply progress_evstep, CoreExit_split.
    + destruct (H _ ltac:(rewrite E; apply measure_Z) _ _ _ _ _ eq_refl _
        (StackT _ _ _ _ HL) (Input_zeros _ _ _ j (InputT _ _ _ HR)))
        as [ww [rr [HN [HW HE]]]].
      exists ww,rr; split; [rewrite <-CV_Z; exact HN|]; split; [arith|].
      follow100 CoreZ; exact HE.
  - destruct (H _ ltac:(rewrite E; apply measure_T) _ _ _ _ _ eq_refl _
      (StackT _ _ _ _ HS) HR) as [ww [rr [HN [HW HE]]]].
    exists ww,rr; split; [rewrite <-CV_T; exact HN|]; split; [arith|].
    follow100 CoreT; exact HE.
  - destruct (H _ ltac:(rewrite E; apply measure_D) _ _ _ _ _ eq_refl _
      (StackD _ _ _ _ HS) HR) as [ww [rr [HN [HW HE]]]].
    exists ww,rr; split; [rewrite <-CV_D; exact HN|]; split; [arith|].
    follow100 CoreD; exact HE.
Qed.

Lemma CoreCall l h m:
  exists w r, Num ((m*12+8)*2^h) w r /\ w<=m*2^(h+1) /\
    l |> rd1^^h *> rm3 *> RC m -->+ l <| r.
Proof.
  destruct (CoreReturn l h 1 1 _ _ _ _ (StackD _ _ _ _ (StackNil _)) (InputEnd m))
    as [w [r [HN [HW HE]]]].
  exists w,r; split; [|split; [exact HW|follow10 CoreEnter; exact HE]].
  replace ((m*12+8)*2^h) with (CV h 1 1 (m*6)) by (unfold CV; arith).
  exact HN.
Qed.

Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; follow10 HX; finish.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc n l: l |> RC n -->+ l <| RC (1+n).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma RC_ones n a: rd1^^a *> RC n = RC ((n+1)*2^a-1).
Proof.
  induction a.
  - cbn [lpow]; replace ((n+1)*2^0-1) with n by arith; reflexivity.
  - rewrite lpow_S; change (rd1 *> (rd1^^a *> RC n) = RC ((n+1)*2^S a-1)).
    rewrite IHa; unfold RC.
    replace ((n+1)*2^S a-1) with (((n+1)*2^a-1)*2+1) by arith.
    rewrite BinInc_mul2add1; reflexivity.
Qed.

Lemma RNum n w r: Num n w r -> forall l a,
  exists w' r', Num ((n+1)*2^a) w' r' /\ w'<=w*2^a /\
    l |> rd1^^a *> r -->+ l <| r'.
Proof.
  induction 1 as [n|m|m|n w r H IH|n w r H IH]; intros l a.
  - exists 0%nat,(RC ((n+1)*2^a)); split; [apply NumOrd|]; split; [lia|].
    rewrite RC_ones.
    assert (0<(n+1)*2^a) by arith.
    applys_eq (RC_Inc ((n+1)*2^a-1) l); flia.
  - exists (m*2^a),(rd0^^a *> [1;0;0] *> RC m); repeat split.
    + apply Num_zeros,NumShort1.
    + lia.
    + follow10 RInc; finish.
  - divmod2_cases m.
    + exists (n'*2^(a+1)),(rd0^^(a+1) *> [1;0;0] *> RC n'); split.
      * replace ((n'*2*6+1+1)*2^a) with ((n'*6+1)*2^(a+1)) by arith.
        apply Num_zeros,NumShort1.
      * split; [arith|]. unfold RC; rewrite BinInc_mul2; cbn [BinaryCounter.d0].
        change (l |> rd1^^a *> rd1 *> [0;0;0] *> RC n' -->+
          l <| rd0^^(a+1) *> [1;0;0] *> RC n').
        rewrite lpow_add' with (n2:=1%nat).
        follow10 RInc; finish.
    + destruct (CoreCall l a n') as [w [r [HN [HW HE]]]].
      exists w,r; split.
      * replace (((n'*2+1)*6+1+1)*2^a) with ((n'*12+8)*2^a) by arith; exact HN.
      * split; [arith|]. unfold RC; rewrite BinInc_mul2add1; exact HE.
  - exists (w*2*2^a),(rd0^^a *> rd1 *> r); repeat split.
    + apply Num_zeros,NumD,H.
    + lia.
    + follow10 RInc; finish.
  - destruct (IH l (a+1)) as [w' [r' [HN [HW HE]]]].
    exists w',r'; split.
    + replace ((n*2+1+1)*2^a) with ((n+1)*2^(a+1)) by arith; exact HN.
    + split; [arith|].
      change (l |> rd1^^a *> rd1 *> r -->+ l <| r').
      rewrite lpow_add' with (n2:=1%nat); exact HE.
Qed.

Lemma Num_step n w r l: Num n w r ->
  exists w' r', Num (n+1) w' r' /\ w'<=w /\ l |> r -->+ l <| r'.
Proof.
  intros H; destruct (RNum _ _ _ H l 0) as [w' [r' [HN [HW HE]]]].
  cbn [Nat.pow lpow] in *; repeat rewrite Nat.mul_1_r in *; eauto 8.
Qed.

Lemma Num_increments len k n w r: k<2^len -> Num n w r ->
  exists w' r', Num (n+k+1) w' r' /\ w'<=w /\
    LC len k |> r -->+ LC len 0 <| r'.
Proof.
  gen n w r; induction k; intros n w r HK HN.
  - rewrite Nat.add_0_r; apply Num_step,HN.
  - destruct (Num_step _ _ _ (LC len (S k)) HN) as [w1 [r1 [HN1 [HW1 HE1]]]].
    destruct (IHk _ _ _ ltac:(lia) HN1) as [w2 [r2 [HN2 [HW2 HE2]]]].
    exists w2,r2; split.
    + applys_eq HN2; flia.
    + split; [lia|]. follow11 HE1.
      change (LC len (1+k) <| r1 -->+ LC len 0 <| r2).
      eapply progress_trans; [apply LC_Inc; lia|exact HE2].
Qed.
Lemma Finish_num len k n w r: k<2^len -> w*8<=n+k+1 -> Num n w r ->
  LC len k |> r -->+ LC len 0 <| RC (n+k+1).
Proof.
  intros HK HB HN; destruct (Num_increments _ _ _ _ _ HK HN) as [w' [r' [HN' [HW HE]]]].
  assert (w'=0%nat) by (pose proof (Num_bound _ _ _ HN'); lia).
  rewrite (Num_ordinary _ _ _ HN' H) in HE; exact HE.
Qed.

Definition RP h n r := BinDec2 [0] [1] [0;0;0] h n r.
Lemma RP_Inc len n r l: 1+n<2^(len+1) -> l |> RP len (1+n) r -->+ l <| RP len n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.
Lemma RP_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> RP h n r -->* LC len k |> RP h 0 r.
Proof.
  gen k; induction n; intros k HK Hn; [finish|].
  eapply evstep_trans; [apply progress_evstep,RP_Inc; lia|].
  rewrite Nat.add_succ_r.
  eapply evstep_trans; [apply progress_evstep,LC_Inc; lia|].
  follow IHn; try lia; finish.
Qed.
Lemma RP_init h r: RP h (2^(h+1)-2) r = [1] *> rd0^^h *> r.
Proof.
  unfold RP; replace (2^(h+1)-2) with ((2^h-1)*2) by arith.
  rewrite BinDec2_mul2; cbn [List.app]; rewrite BinDec_full; reflexivity.
Qed.
Lemma Low_run len k h r: k+(2^(h+1)-2)<2^len ->
  LC len (k+(2^(h+1)-2)) |> [1] *> rd0^^h *> r -->*
  LC len k |> rd1^^h *> [1] *> r.
Proof.
  intros HK; rewrite <-RP_init.
  change (LC len (k+(2^(h+1)-2)) |> RP h (2^(h+1)-2) r -->*
    LC len k |> ([1]++[0;0;0])^^h *> [1] *> r).
  rewrite <-(BinDec2_O [0] [1] [0;0;0]); apply RP_Incs; arith.
Qed.
Lemma LC_Ov len r: LC len 0 <| r -->+ LC len (2^len-1) |> [1] *> r.
Proof. unfold LC; rewrite BinDec_O,BinDec_full; apply LOv. Qed.
Lemma LC_Append len k h r: k<2^len ->
  LC len k |> rd1^^h *> rm1 *> r -->+
  LC (len+1+h*2) ((k*2+1)*2^(h*2)-1) |> [1;0;0] *> r.
Proof.
  intros HK; unfold LC; follow10 ROv1.
  rewrite BinDec_mulpow2sub1 by arith; finish.
Qed.
Lemma pow_double h: 2^(h*2)=2^h*2^h.
Proof. replace (h*2) with (h+h) by lia; apply Nat.pow_add_r. Qed.
Lemma round_budget len h: h<len ->
  2^len*2-2 <= (((2^len+1-2^(h+1))*2+1)*2^(h*2)-1) < 2^(len+1+h*2).
Proof.
  intros Hh.
  assert (2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  repeat rewrite Nat.pow_add_r; repeat rewrite pow_double; arith.
Qed.

Definition cfg len n := LC len 0 <| RC n.
Definition next_value len h m := (2^len*2+3-2^(h+2))*2^(h*2)+m*6+1.
Lemma Round len h m: h<len -> m<2^len ->
  cfg len ((m*2+1)*2^h) -->+ cfg (len+1+h*2) (next_value len h m).
Proof.
  intros Hh Hm.
  assert (HP: 2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  pose proof (round_budget len h Hh) as [HB HK].
  unfold cfg; follow10 LC_Ov.
  unfold RC; rewrite BinInc_mulpow2,BinInc_mul2add1; cbn [BinaryCounter.d0]; fold RC.
  replace (2^len-1) with ((2^len+1-2^(h+1))+(2^(h+1)-2)) by arith.
  eapply evstep_trans; [apply Low_run; arith|].
  eapply evstep_trans; [apply progress_evstep,LC_Append; arith|].
  replace (next_value len h m) with
    (m*6+1+(((2^len+1-2^(h+1))*2+1)*2^(h*2)-1)+1) by (unfold next_value; arith).
  apply progress_evstep,Finish_num with (w:=m); try lia; apply NumShort1.
Qed.

Inductive Valid: nat -> nat -> Prop :=
| ValidOdd len m: 2<=len -> 0<m -> (m*2+1)*3<2^len*5 -> Valid len (m*2+1)
| ValidEven len m: 2<=len -> 0<m -> (2^len+m*6)*2<2^len*7 -> Valid len (2^len+m*6).

Lemma pow_three len: 2^len mod 3 <> 0%nat.
Proof.
  induction len; [cbn; lia|].
  rewrite Nat.pow_succ_r',Nat.Div0.mul_mod.
  pose proof (Nat.mod_upper_bound (2^len) 3 ltac:(lia)).
  destruct (2^len mod 3) as [|[|[|r]]]; cbn in *; lia.
Qed.
Lemma even_guard len k h m: 0<k -> (2^len+k*6)*2<2^len*7 ->
  2^len+k*6=(m*2+1)*2^h -> h<len.
Proof.
  intros HK HB E; destruct (Nat.lt_ge_cases h len); [assumption|].
  replace h with (len+(h-len)) in E by lia; rewrite Nat.pow_add_r in E.
  remember ((m*2+1)*2^(h-len)) as q.
  assert (EQ: 2^len+k*6=q*2^len) by nia.
  assert (q=2%nat \/ q=3%nat) by nia.
  exfalso; apply (pow_three len); destruct H0; subst q.
  - replace (2^len) with ((k*2)*3) by nia; apply Nat.Div0.mod_mul.
  - replace (2^len) with (k*3) by nia; apply Nat.Div0.mod_mul.
Qed.
Lemma Valid_split len n: Valid len n -> forall h m,
  n=(m*2+1)*2^h -> h<len /\ m<2^len.
Proof.
  destruct 1 as [len k HL HK HB|len k HL HK HB]; intros h m E.
  - destruct h.
    + cbn [Nat.pow] in E; split; lia.
    + rewrite Nat.pow_succ_r' in E; lia.
  - split; [eapply even_guard; eauto|].
    destruct h.
    + destruct len; [lia|]; rewrite Nat.pow_succ_r' in E; cbn [Nat.pow] in E; lia.
    + assert (2<=2^S h) by arith; nia.
Qed.
Lemma even_next_bound len h m: 0<h -> h<len ->
  ((m*2+1)*2^h)*2<2^len*7 ->
  next_value len h m * 3 < 2^(len+1+h*2)*5.
Proof.
  intros Hh HL HB.
  assert (HA: 2<=2^h) by (change (2^1<=2^h); apply Nat.pow_le_mono_r; lia).
  assert (HC: 2^(h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
  assert (Hm: m*8<2^len*7) by nia.
  unfold next_value; repeat rewrite Nat.pow_add_r; repeat rewrite pow_double; arith.
Qed.
Lemma Valid_next len n h m: Valid len n -> n=(m*2+1)*2^h ->
  Valid (len+1+h*2) (next_value len h m).
Proof.
  intros HV E; pose proof (Valid_split _ _ HV _ _ E) as [HH HM].
  destruct HV as [len k HL HK HB|len k HL HK HB].
  - destruct h; [|rewrite Nat.pow_succ_r' in E; lia].
    assert (k=m) by (cbn [Nat.pow] in E; lia); subst k.
    replace (len+1+0*2) with (len+1) by lia.
    replace (next_value len 0 m) with (2^(len+1)+m*6) by (unfold next_value; arith).
    apply ValidEven; try lia; arith.
  - destruct h.
    + destruct len; [lia|]; rewrite Nat.pow_succ_r' in E; cbn [Nat.pow] in E; lia.
    + pose proof (even_next_bound len (S h) m ltac:(lia) HH ltac:(rewrite <-E; exact HB)) as HN.
      assert (HP: 2^(S h+1)<=2^len) by (apply Nat.pow_le_mono_r; lia).
      set (q := (2^len*2+3-2^(S h+2))*2^(h*2+1)+m*3).
      assert (EN: next_value len (S h) m=q*2+1).
      { unfold next_value,q; replace (S h*2) with (h*2+1+1) by lia; arith. }
      rewrite EN; apply ValidOdd; try lia; unfold q; arith.
Qed.
Lemma cfg_nonhalt len n: Valid len n -> ~halts tm (cfg len n).
Proof.
  intros HV.
  apply (progress_nonhalt_cond tm (nat*nat) (len,n)
    (fun '(l,n)=>cfg l n) (fun '(l,n)=>Valid l n)).
  - intros [L n0] H.
    lowbit_cases n0.
    + inversion H; lia.
    + pose proof (Valid_split _ _ H i x eq_refl) as [HH HM].
      exists (L+1+i*2,next_value L i x); split; [apply Round; assumption|].
      eapply Valid_next; [exact H|reflexivity].
  - exact HV.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  eapply multistep_nonhalt with (c':=cfg 4 11).
  - change (LC 4 (1+9) <| RC 1 -->* cfg 4 11).
    eapply evstep_trans; [apply progress_evstep,LC_Inc; cbn; lia|].
    unfold cfg; apply progress_evstep,Finish_num with (n:=1%nat) (w:=0%nat); try (cbn; lia); apply NumOrd.
  - apply cfg_nonhalt.
    change (Valid 4 (5*2+1)); apply ValidOdd; cbn; lia.
Qed.
End TM166.
