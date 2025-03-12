From BusyCoq Require Import Individual62 BinaryCounter BinaryCounterFull NatMod.
Require Import Lia List NArith PeanoNat.

Definition BinDec d0 d1 len n r :=
  BinaryCounter d0 d1 r (Pos.of_nat (2^(len+1)-1-n)).

Definition BinDec2 d0 d1 dw len n r :=
  match n mod 2 with
  | O => d1
  | _ => d0
  end *>
  BinDec (dw++d0) (dw++d1) len (n/2) r.

Definition BinInc d1 n :=
  BinaryCounter_0 d1 (N.of_nat n).

Lemma RBinInc_spec d1 tm QL QR qL qR:
  (forall l r n,
  l <* qR {{QR}}> d1^^n *> (d0 d1) *> r -[ tm ]->+
  l <{{QL}} qL *> (d0 d1)^^n *> d1 *> r) ->
  forall n l,
  l <* qR {{QR}}> BinInc d1 n -[ tm ]->+
  l <{{QL}} qL *> BinInc d1 (1+n).
Proof.
  unfold BinInc.
  intros H n l.
  replace (N.of_nat (1+n)) with (N.succ (N.of_nat n)) by lia.
  apply RInc_0,H.
Qed.

Lemma log2_spec' n x:
  2^n <= x < 2^(n+1) ->
  log2 (Pos.of_nat x) = n.
Proof.
  gen x.
  induction n; intros.
  - cbn in H.
    replace x with 1%nat by lia.
    reflexivity.
  - cbn in H.
    destruct (Pos.of_nat x) eqn:E.
    + cbn.
      f_equal.
      applys_eq (IHn (Pos.to_nat p)).
      1: f_equal; lia.
      cbn; lia.
    + cbn.
      f_equal.
      applys_eq (IHn (Pos.to_nat p)).
      1: f_equal; lia.
      cbn; lia.
    + pose proof (Nat.pow_nonzero 2 n).
      lia.
Qed.

Lemma pow2_S n:
  2^(n+1) = 2^n*2.
Proof.
  rewrite Nat.pow_add_r; cbn; lia.
Qed.

Lemma pow2_spec' n:
  pow2 n = (Pos.of_nat (2^n)).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Lemma pow2'_spec' n:
  pow2' n = (Pos.of_nat (2^(n+1)-1)).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  pose proof (pow2_S n).
  pose proof (Nat.pow_nonzero 2 n).
  lia.
Qed.

Lemma LBinDec_spec d0 d1 tm QL QR qL qR:
  (forall l r n,
  l <* d0 <* d1^^n <{{QL}} qL *> r -[ tm ]->+
  l <* d1 <* d0^^n <* qR {{QR}}> r) ->
  forall len n l r,
  1+n<2^len ->
  BinDec d0 d1 len (1+n) l <{{QL}} qL *> r -[ tm ]->+
  BinDec d0 d1 len n l <* qR {{QR}}> r.
Proof.
  unfold BinDec.
  intros.
  pose proof (pow2_S len).
  replace (Pos.of_nat (2^(len+1)-1-n)) with (Pos.succ (Pos.of_nat (2^(len+1)-1-(1+n)))) by lia.
  apply LInc.
  1: apply H.
  rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len).
  2: lia.
  rewrite pow2'_spec'.
  lia.
Qed.

Lemma RBinDec_spec d0 d1 tm QL QR qL qR:
  (forall l r n,
  l <* qR {{QR}}> d1^^n *> d0 *> r -[ tm ]->+
  l <{{QL}} qL *> d0^^n *> d1 *> r) ->
  forall len n l r,
  1+n<2^len ->
  l <* qR {{QR}}> BinDec d0 d1 len (1+n) r -[ tm ]->+
  l <{{QL}} qL *> BinDec d0 d1 len n r.
Proof.
  unfold BinDec.
  intros.
  pose proof (pow2_S len).
  replace (Pos.of_nat (2^(len+1)-1-n)) with (Pos.succ (Pos.of_nat (2^(len+1)-1-(1+n)))) by lia.
  apply RInc.
  1: apply H.
  rewrite not_full_iff_pow2'.
  erewrite (log2_spec' len).
  2: lia.
  rewrite pow2'_spec'.
  lia.
Qed.

Lemma RBinDec2_spec d0 d1 dw tm QL QR qL qR:
  (forall l r n,
  l <* qR {{QR}}> (d1++dw)^^n *> d0 *> r -[ tm ]->+
  l <{{QL}} qL *> (d0++dw)^^n *> d1 *> r) ->
  forall len n l r,
  1+n<2^(len+1) ->
  l <* qR {{QR}}> BinDec2 d0 d1 dw len (1+n) r -[ tm ]->+
  l <{{QL}} qL *> BinDec2 d0 d1 dw len n r.
Proof.
  unfold BinDec2.
  intros.
  pose proof (Nat.Div0.div_mod (1+n) 2).
  pose proof (Nat.Div0.div_mod (n) 2).
  pose proof (Nat.mod_upper_bound (1+n) 2).
  pose proof (Nat.mod_upper_bound n 2).
  destruct ((1+n) mod 2) as [|[|]] eqn:E.
  3: lia.
  - destruct (n mod 2) as [|[|]] eqn:E0.
    1,3: lia.
    replace ((1+n)/2) with (1+n/2) by lia.
    unfold BinDec.
    pose proof (pow2_S len).
    replace (Pos.of_nat (2^(len+1)-1-n/2)) with (Pos.succ (Pos.of_nat (2^(len+1)-1-(1+n/2)))) by lia.
    epose proof (not_full_Inc (dw++d0) (dw++d1) r _) as [s [i [HA HB]]].
    rewrite HA,HB.
    epose proof (H _ _ (S i)) as H'.
    cbn in H'.
    gen H'.
    repeat rewrite Str_app_assoc.
    repeat rewrite lpow_rotate'.
    apply (fun x=>x).
    Unshelve.
    rewrite not_full_iff_pow2'.
    erewrite (log2_spec' len).
    2: lia.
    rewrite pow2'_spec'.
    lia.
  - destruct (n mod 2) as [|[|]] eqn:E0.
    2,3: lia.
    replace ((1+n)/2) with (n/2) by lia.
    epose proof (H _ _ O) as H'.
    cbn in H'.
    apply H'.
Qed.

Lemma BinDec_O d0 d1 len r:
  BinDec d0 d1 len O r =
  d1^^len *> r.
Proof.
  unfold BinDec.
  erewrite <-Counter_pow2'.
  rewrite pow2'_spec'.
  f_equal.
  lia.
Qed.

Lemma BinDec_full d0 d1 len r:
  BinDec d0 d1 len (2^len-1) r =
  d0^^len *> r.
Proof.
  unfold BinDec.
  erewrite <-Counter_pow2.
  rewrite pow2_spec'.
  do 2 f_equal.
  pose proof (pow2_S len).
  lia.
Qed.

Lemma pow2'_S n:
  2^(S n)*2-1 = (2^n*2-1)*2+1.
Proof.
  induction n.
  1: reflexivity.
  gen IHn.
  cbn; lia.
Qed.

Lemma pow2'_div2 n:
  ((2^n*2-1) / 2 = 2^n-1)%nat.
Proof.
  induction n.
  1: reflexivity.
  rewrite pow2'_S.
  rewrite Nat.div_add_l.
  2: lia.
  cbn.
  lia.
Qed.

Lemma pow2'_mod2 n:
  ((2^n*2-1) mod 2 = 1)%nat.
Proof.
  induction n.
  1: reflexivity.
  rewrite pow2'_S.
  rewrite Nat.Div0.add_mod.
  rewrite Nat.Div0.mul_mod.
  rewrite IHn.
  reflexivity.
Qed.

Definition to_digits (d0 d1:list Sym) ls :=
  flat_map (fun n => match n with O => d0 | _ => d1 end) ls.

Lemma BinDec_mul2add1 d0 d1 len n r:
  n*2+1 < 2^(len+1) ->
  BinDec d0 d1 (len+1) (n*2+1) r =
  d0 *> BinDec d0 d1 len n r.
Proof.
  unfold BinDec.
  repeat rewrite pow2_S.
  intros H.
  pose proof (Nat.pow_nonzero 2 (len)).
  replace (Pos.of_nat (2 ^ len * 2 * 2 - 1 - (n * 2 + 1))) with (xO (Pos.of_nat (2 ^ len * 2 - 1 - n))) by lia.
  reflexivity.
Qed.

Lemma BinDec_mul2 d0 d1 len n r:
  n*2 < 2^(len+1) ->
  BinDec d0 d1 (len+1) (n*2) r =
  d1 *> BinDec d0 d1 len n r.
Proof.
  unfold BinDec.
  repeat rewrite pow2_S.
  intros H.
  pose proof (Nat.pow_nonzero 2 (len)).
  replace (Pos.of_nat (2 ^ len * 2 * 2 - 1 - (n * 2))) with (xI (Pos.of_nat (2 ^ len * 2 - 1 - n))) by lia.
  reflexivity.
Qed.

Lemma BinDec_mulpow2 d0 d1 len n i r:
  n*2^i < 2^(len+i) ->
  BinDec d0 d1 (len+i) (n*2^i) r =
  d1^^i *> BinDec d0 d1 len n r.
Proof.
  induction i.
  - cbn.
    intros H.
    f_equal; lia.
  - replace (S i) with (i+1) by lia.
    rewrite Nat.add_assoc.
    repeat rewrite pow2_S.
    repeat rewrite Nat.mul_assoc.
    intros H.
    rewrite BinDec_mul2. 2: rewrite pow2_S; lia.
    rewrite IHi.
    2: lia.
    simpl_tape.
    simpl_tape.
    reflexivity.
Qed.

Lemma mulpow2sub1 n i:
  (n*2+1)*2^i*2-1 =
  ((n*2+1)*2^i-1)*2+1.
Proof.
  pose proof (Nat.pow_nonzero 2 i).
  lia.
Qed.

Lemma BinDec_mulpow2sub1 d0 d1 len n i r:
  (n*2+1)*2^i-1 < 2^(len+1+i) ->
  BinDec d0 d1 (len+1+i) ((n*2+1)*2^i-1) r =
  d0^^i *> d1 *> BinDec d0 d1 len n r.
Proof.
  induction i.
  - cbn.
    intros H.
    rewrite Nat.add_0_r.
    replace ((n*2+1)*1-1) with (n*2) by lia.
    rewrite BinDec_mul2.
    1: reflexivity.
    rewrite Nat.add_0_r in *.
    lia.
  - replace (S i) with (i+1) by lia.
    repeat rewrite Nat.add_assoc.
    repeat rewrite pow2_S.
    repeat rewrite Nat.mul_assoc.
    rewrite mulpow2sub1.
    intros H.
    rewrite BinDec_mul2add1.
    2: repeat rewrite Nat.pow_add_r in *; cbn in *; lia.
    rewrite IHi.
    2: lia.
    simpl_tape.
    simpl_tape.
    reflexivity.
Qed.

Lemma BinDec_app d0 d1 ls len n r:
  n<2^(len) ->
  exists k,
  to_digits d0 d1 ls *> BinDec d0 d1 len n r =
  BinDec d0 d1 (len+(length ls)) k r /\
  k < 2^(len+(length ls)) /\
  2^(length ls)*n <= k < 2^(length ls)*(n+1).
Proof.
  unfold to_digits.
  intros Hn.
  induction ls.
  - exists n.
    cbn.
    split.
    1: f_equal; lia.
    rewrite Nat.add_0_r.
    lia.
  - destruct IHls as [k [H0 [H1 H2]]].
    destruct a.
    + exists (k*2+1).
      cbn[flat_map].
      rewrite Str_app_assoc.
      rewrite H0.
      split.
      * cbn.
        rewrite <-Nat.add_1_r,Nat.add_assoc.
        rewrite BinDec_mul2add1.
        1: reflexivity.
        rewrite pow2_S.
        lia.
      * cbn.
        rewrite (Nat.add_succ_r len).
        cbn; lia.
    + exists (k*2).
      cbn[flat_map].
      rewrite Str_app_assoc.
      rewrite H0.
      split.
      * cbn.
        rewrite <-Nat.add_1_r,Nat.add_assoc.
        rewrite BinDec_mul2.
        1: reflexivity.
        rewrite pow2_S.
        lia.
      * cbn.
        rewrite (Nat.add_succ_r len).
        cbn; lia.
Qed.


Lemma BinDec2_O d0 d1 dw len r:
  BinDec2 d0 d1 dw len O r =
  (d1++dw)^^len *> d1 *> r.
Proof.
  unfold BinDec2.
  cbn.
  rewrite BinDec_O.
  rewrite lpow_rotate'.
  reflexivity.
Qed.

Lemma BinDec2_full d0 d1 dw len r:
  BinDec2 d0 d1 dw len (2^(len+1)-1) r =
  (d0++dw)^^len *> d0 *> r.
Proof.
  unfold BinDec2.
  rewrite pow2_S.
  rewrite pow2'_mod2,pow2'_div2.
  rewrite BinDec_full.
  rewrite lpow_rotate'.
  reflexivity.
Qed.

Lemma BinDec2_mul2 d0 d1 dw len n r:
  BinDec2 d0 d1 dw len (n*2) r =
  d1 *> BinDec (dw++d0) (dw++d1) len n r.
Proof.
  unfold BinDec2.
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.div_mul.
  1: reflexivity.
  lia.
Qed.

Lemma BinInc_O d1:
  BinInc d1 O =
  0inf.
Proof.
  reflexivity.
Qed.

Lemma BinInc_1 d1:
  BinInc d1 1 =
  d1 *> 0inf.
Proof.
  reflexivity.
Qed.

Lemma BinInc_mul2 d1 n:
  BinInc d1 (n*2) =
  (d0 d1) *> BinInc d1 n.
Proof.
  unfold BinInc.
  applys_eq (BinaryCounter_0_d0').
  f_equal; lia.
Qed.

Lemma BinInc_mul2add1 d1 n:
  BinInc d1 (n*2+1) =
  d1 *> BinInc d1 n.
Proof.
  unfold BinInc.
  applys_eq (BinaryCounter_0_d1').
  f_equal; lia.
Qed.

Lemma BinInc_mulpow2 d1 n i:
  BinInc d1 (n*2^i) =
  (d0 d1)^^i *> BinInc d1 n.
Proof.
  induction i.
  1: cbn; f_equal; lia.
  replace (n*2^S i) with (n*2^i*2) by (cbn; lia).
  rewrite BinInc_mul2,IHi.
  cbn.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Inductive lowbit: nat->Prop :=
| lowbit_O: lowbit O
| lowbit_S x i: lowbit ((x*2+1)*2^i)
.

Lemma lowbit_cases' n:
  lowbit n.
Proof.
  induction n using strong_induction.
  destruct n as [|n].
  1: constructor.
  pose proof (Nat.Div0.div_mod (S n) 2).
  pose proof (Nat.mod_upper_bound (S n) 2).
  destruct (S n mod 2) as [|[|]].
  3: lia.
  - remember (S n / 2) as n'.
    epose proof (H n' _) as H.
    inversion H.
    1: lia.
    applys_eq (lowbit_S x (S i)).
    cbn. lia.
  - applys_eq (lowbit_S (S n/2) O).
    cbn in *. lia.
  Unshelve.
  lia.
Qed.

Ltac lowbit_cases n :=
  pose proof (lowbit_cases' n) as HX;
  inverts HX.

Lemma split_bound_v1 x i n:
  (x*2+1)*2^i < 2^n ->
  2^i*2 + x < 2^n + 1.
Proof.
  gen x n.
  induction i; intros.
  1: cbn in *; lia.
  cbn[Nat.pow].
  destruct n as [|n].
  1: pose proof (Nat.pow_nonzero 2 i);
    cbn in *; lia.
  cbn[Nat.pow].
  specialize (IHi x n).
  cbn in *; lia.
Qed.

Lemma split_bound_v2 x i:
  2^i*2 + x < (x*2+1)*2^i*2 + 1.
Proof.
  induction i.
  1: cbn; lia.
  cbn[Nat.pow].
  lia.
Qed.

Lemma le_pow2_v1 a b c:
  a <= b ->
  a <= b*(2^c).
Proof.
  pose proof (Nat.pow_nonzero 2 c).
  replace (2^c) with (1+(2^c-1)) by lia.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_1_r.
  apply Arith_base.le_plus_trans_stt.
Qed.

Lemma lt_pow2_v1 a b c:
  a < b ->
  a < b*2^c.
Proof.
  pose proof (Nat.pow_nonzero 2 c).
  replace (2^c) with (1+(2^c-1)) by lia.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_1_r.
  remember (b*(2^c-1)) as v1.
  lia.
Qed.

Lemma lt_le_sub1 a b:
  a<b ->
  a<=b-1.
Proof.
  lia.
Qed.

Lemma lt_sub1 a b:
  a<b ->
  a-1<b.
Proof.
  lia.
Qed.

Opaque BinDec BinDec2 BinInc.

Ltac rw_Bin :=
  repeat (
  rewrite BinDec_O ||
  rewrite BinDec_full ||
  rewrite BinDec_mul2 ||
  rewrite BinDec_mul2add1 ||
  rewrite BinDec_mulpow2 ||
  rewrite BinDec_mulpow2sub1 ||
  rewrite BinDec2_O ||
  rewrite BinDec2_mul2 ||
  rewrite BinInc_mulpow2 ||
  rewrite BinInc_O ||
  rewrite BinInc_1 ||
  rewrite BinInc_mul2 ||
  rewrite BinInc_mul2add1
  ).

Ltac simpl_flat_map :=
  repeat rewrite flat_map_app in *;
  repeat rewrite flat_map_lpow in *;
  cbn[flat_map] in *;
  repeat rewrite app_nil_r in *;
  repeat rewrite Str_app_assoc in *.

Ltac simpl_length :=
  repeat (
  rewrite length_app in * ||
  rewrite lpow_length in *);
  cbn[length] in *.

