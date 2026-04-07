From Coq Require Import Uint63 ZArith Lia Lists.List Arith.PeanoNat Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof.

Import ListNotations.
Local Open Scope Z_scope.

Ltac rewrite_index_eq H := first [rewrite H | rewrite <- H].

Lemma u63_of_nat_neq :
  forall m n,
    (Z.of_nat m < Uint63.wB)%Z ->
    (Z.of_nat n < Uint63.wB)%Z ->
    m <> n ->
    u63_of_nat m <> u63_of_nat n.
Proof.
  intros m n Hm Hn Hneq Heq.
  apply Hneq.
  eapply u63_of_nat_inj; eauto.
Qed.

Lemma coeff_array_make_length :
  forall n,
    (Z.of_nat n <= Uint63.to_Z PArray.max_length)%Z ->
    PArray.length (coeff_array_make n) = u63_of_nat n.
Proof.
  intros n Hn.
  unfold coeff_array_make.
  rewrite PArray.length_make.
  unfold u63_of_nat.
  assert (Hleb : (Uint63.of_Z (Z.of_nat n) ≤? PArray.max_length)%uint63 = true).
  {
    apply Uint63.leb_spec.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    - exact Hn.
    - split.
      + lia.
      + eapply Z.le_lt_trans; [apply Hn|].
        apply Uint63.to_Z_bounded.
  }
  rewrite Hleb.
  reflexivity.
Qed.

Lemma coeff_array_set_if_in_bounds_same :
  forall arr idx value,
    (idx <? PArray.length arr)%uint63 = true ->
    PArray.get (coeff_array_set_if_in_bounds arr idx value) idx = value.
Proof.
  intros arr idx value Hidx.
  unfold coeff_array_set_if_in_bounds.
  rewrite Hidx.
  apply PArray.get_set_same.
  exact Hidx.
Qed.

Lemma coeff_array_set_if_in_bounds_other :
  forall arr idx value j,
    idx <> j ->
    PArray.get (coeff_array_set_if_in_bounds arr idx value) j =
    PArray.get arr j.
Proof.
  intros arr idx value j Hneq.
  unfold coeff_array_set_if_in_bounds.
  destruct (Uint63.ltb idx (PArray.length arr)) eqn:Hidx.
  - apply PArray.get_set_other.
    exact Hneq.
  - reflexivity.
Qed.

Lemma coeff_array_set_if_in_bounds_length :
  forall arr idx value,
    PArray.length (coeff_array_set_if_in_bounds arr idx value) = PArray.length arr.
Proof.
  intros arr idx value.
  unfold coeff_array_set_if_in_bounds.
  destruct (Uint63.ltb idx (PArray.length arr)) eqn:Hidx.
  - apply PArray.length_set.
  - reflexivity.
Qed.

Lemma index_bound_upto_7 :
  forall base step j,
    (j < 8)%nat ->
    (base + step * j <= base + 7 * step)%nat.
Proof.
  intros base step j Hj.
  assert (Hmul : (step * j <= step * 7)%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma u63_of_nat_index_ltb_length :
  forall len idx,
    (idx < len)%nat ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (u63_of_nat idx <? u63_of_nat len)%uint63 = true.
Proof.
  intros len idx Hidx Hlen.
  apply u63_of_nat_ltb; assumption.
Qed.

Lemma u63_of_nat_index_neq :
  forall len i j,
    (i < len)%nat ->
    (j < len)%nat ->
    (Z.of_nat len < Uint63.wB)%Z ->
    i <> j ->
    u63_of_nat i <> u63_of_nat j.
Proof.
  intros len i j Hi Hj Hlen Hneq.
  apply u63_of_nat_neq; try exact Hneq.
  - eapply Z.lt_le_trans.
    + apply Nat2Z.inj_lt. exact Hi.
    + lia.
  - eapply Z.lt_le_trans.
    + apply Nat2Z.inj_lt. exact Hj.
    + lia.
Qed.

Lemma nat_lt_len_lt_wB :
  forall n len,
    (n < len)%nat ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Z.of_nat n < Uint63.wB)%Z.
Proof.
  intros n len Hn Hlen.
  eapply Z.lt_trans.
  - apply Nat2Z.inj_lt.
    exact Hn.
  - exact Hlen.
Qed.

Lemma fill_crt_block_get_block_index_0 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat base) =
    crt_combine_u63 (Prime469.b0 x469) (Prime181.b0 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hbase : (base < len)%nat) by lia.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  assert (Hidx1eq :
    block_index_1 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 4 * step)).
  {
    apply block_index_1_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx1.
    exact HlenB.
  }
  assert (Hidx2eq :
    block_index_2 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 2 * step)).
  {
    apply block_index_2_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx2.
    exact HlenB.
  }
  assert (Hidx3eq :
    block_index_3 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 6 * step)).
  {
    apply block_index_3_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx3.
    exact HlenB.
  }
  assert (Hidx4eq :
    block_index_4 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + step)).
  {
    apply block_index_4_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx4.
    exact HlenB.
  }
  assert (Hidx5eq :
    block_index_5 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 5 * step)).
  {
    apply block_index_5_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx5.
    exact HlenB.
  }
  assert (Hidx6eq :
    block_index_6 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 3 * step)).
  {
    apply block_index_6_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx6.
    exact HlenB.
  }
  assert (Hidx7eq :
    block_index_7 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 7 * step)).
  {
    apply block_index_7_nat.
    apply nat_lt_len_lt_wB with len.
    exact Hidx7.
    exact HlenB.
  }
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx4eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_1 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_1 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b1 x469) (Prime181.b1 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx4eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx3eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx2eq, Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx1eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_2 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_2 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b2 x469) (Prime181.b2 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq, Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq, Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx4eq, Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx3eq, Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx2eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_3 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_3 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b3 x469) (Prime181.b3 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq, Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq, Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx4eq, Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx3eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_4 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_4 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b4 x469) (Prime181.b4 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx4eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq, Hidx4eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq, Hidx4eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx4eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_5 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_5 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b5 x469) (Prime181.b5 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx5eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq, Hidx5eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx5eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_6 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_6 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b6 x469) (Prime181.b6 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  pose proof (block_index_1_nat base step
    (nat_lt_len_lt_wB (base + 4 * step) len Hidx1 HlenB)) as Hidx1eq.
  pose proof (block_index_2_nat base step
    (nat_lt_len_lt_wB (base + 2 * step) len Hidx2 HlenB)) as Hidx2eq.
  pose proof (block_index_3_nat base step
    (nat_lt_len_lt_wB (base + 6 * step) len Hidx3 HlenB)) as Hidx3eq.
  pose proof (block_index_4_nat base step
    (nat_lt_len_lt_wB (base + step) len Hidx4 HlenB)) as Hidx4eq.
  pose proof (block_index_5_nat base step
    (nat_lt_len_lt_wB (base + 5 * step) len Hidx5 HlenB)) as Hidx5eq.
  pose proof (block_index_6_nat base step
    (nat_lt_len_lt_wB (base + 3 * step) len Hidx6 HlenB)) as Hidx6eq.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hidx7 HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq, Hidx6eq.
    eapply u63_of_nat_index_neq; eauto.
    lia.
  }
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx6eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma fill_crt_block_get_block_index_7 :
  forall len arr base step x469 x181,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (block_index_7 (u63_of_nat base) (u63_of_nat step)) =
    crt_combine_u63 (Prime469.b7 x469) (Prime181.b7 x181).
Proof.
  intros len arr base step x469 x181 Hstep Hlen HlenB Hrange.
  pose proof (block_index_7_nat base step
    (nat_lt_len_lt_wB (base + 7 * step) len Hrange HlenB)) as Hidx7eq.
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_same.
  2:{
    rewrite Hidx7eq.
    rewrite ?coeff_array_set_if_in_bounds_length.
    rewrite Hlen.
    apply u63_of_nat_index_ltb_length; assumption.
  }
  reflexivity.
Qed.

Lemma coeff_array_from_packed_trees_length :
  forall k arr base step x469 x181,
    PArray.length (coeff_array_from_packed_trees k arr base step x469 x181) =
    PArray.length arr.
Proof.
  induction k as [|k IH]; intros arr base step x469 x181.
  - unfold coeff_array_from_packed_trees, fill_crt_block.
    repeat rewrite coeff_array_set_if_in_bounds_length.
    reflexivity.
  - destruct x469 as [l469 r469], x181 as [l181 r181].
    cbn [coeff_array_from_packed_trees].
    rewrite IH.
    apply IH.
Qed.

Lemma fill_crt_block_preserve_outside :
  forall len arr base step x469 x181 j,
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (j < len)%nat ->
    (base + 7 * step < len)%nat ->
    (forall i, (i < 8)%nat -> j <> (base + step * i)%nat) ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat j) =
    PArray.get arr (u63_of_nat j).
Proof.
  intros len arr base step x469 x181 j Hlen HlenB Hj Hrange Hneq.
  assert (Hbase : (base < len)%nat) by lia.
  assert (Hidx1 : (base + 4 * step < len)%nat) by lia.
  assert (Hidx2 : (base + 2 * step < len)%nat) by lia.
  assert (Hidx3 : (base + 6 * step < len)%nat) by lia.
  assert (Hidx4 : (base + step < len)%nat) by lia.
  assert (Hidx5 : (base + 5 * step < len)%nat) by lia.
  assert (Hidx6 : (base + 3 * step < len)%nat) by lia.
  assert (Hidx7 : (base + 7 * step < len)%nat) by lia.
  assert (Hidx1eq :
    block_index_1 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 4 * step)).
  {
    apply block_index_1_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx2eq :
    block_index_2 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 2 * step)).
  {
    apply block_index_2_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx3eq :
    block_index_3 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 6 * step)).
  {
    apply block_index_3_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx4eq :
    block_index_4 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + step)).
  {
    apply block_index_4_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx5eq :
    block_index_5 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 5 * step)).
  {
    apply block_index_5_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx6eq :
    block_index_6 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 3 * step)).
  {
    apply block_index_6_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  assert (Hidx7eq :
    block_index_7 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 7 * step)).
  {
    apply block_index_7_nat.
    apply nat_lt_len_lt_wB with len; assumption.
  }
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx7eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 7%nat); [lia|].
    replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx6eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 3%nat); [lia|].
    replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx5eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 5%nat); [lia|].
    replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx4eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 1%nat); [lia|].
    replace (base + step * 1)%nat with (base + step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx3eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 6%nat); [lia|].
    replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx2eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 2%nat); [lia|].
    replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hidx1eq.
    eapply u63_of_nat_index_neq; eauto.
    intro Heq.
    apply (Hneq 4%nat); [lia|].
    replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    apply u63_of_nat_neq.
    - eapply Z.lt_trans.
      + apply Nat2Z.inj_lt.
        exact Hbase.
      + exact HlenB.
    - eapply Z.lt_trans.
      + apply Nat2Z.inj_lt.
        exact Hj.
      + exact HlenB.
    - intro Heq.
      apply (Hneq 0%nat); [lia|].
      replace (base + step * 0)%nat with base by lia.
      symmetry.
      exact Heq.
  }
  reflexivity.
Qed.

Lemma coeff_array_from_packed_trees_preserve_outside :
  forall k len arr base step x469 x181 j,
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (j < len)%nat ->
    (base + step * (Prime469.pow2 (S (S (S k))) - 1) < len)%nat ->
    (forall i, (i < Prime469.pow2 (S (S (S k))))%nat -> j <> (base + step * i)%nat) ->
    PArray.get (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat j) =
    PArray.get arr (u63_of_nat j).
Proof.
  induction k as [|k IH]; intros len arr base step x469 x181 j Hlen HlenB Hj Hbound Hneq.
  - change (Prime469.pow2 3) with 8%nat in Hbound.
    replace (base + step * (8 - 1))%nat with (base + 7 * step)%nat in Hbound by lia.
    eapply fill_crt_block_preserve_outside.
    + exact Hlen.
    + exact HlenB.
    + exact Hj.
    + exact Hbound.
    + intros i Hi.
      apply Hneq.
      change (Prime469.pow2 3) with 8%nat.
      exact Hi.
  - destruct x469 as [l469 r469], x181 as [l181 r181].
    cbn [coeff_array_from_packed_trees].
    set (step2 := (step + step)%nat).
    set (arr1 := coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step2) l469 l181).
    assert (Hbound_left :
      (base + step2 * (Prime469.pow2 (S (S (S k))) - 1) < len)%nat).
    {
      subst step2.
      rewrite Prime469.pow2_succ in Hbound.
      eapply Nat.le_lt_trans with
        (m := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      * pose proof (prime469_even_subtree_bound_le_parent k base step) as Hnat.
        lia.
      * exact Hbound.
    }
    assert (Hbound_right :
      (base + step + step2 * (Prime469.pow2 (S (S (S k))) - 1) < len)%nat).
    {
      subst step2.
      rewrite Prime469.pow2_succ in Hbound.
      replace (base + step + (step + step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with (base + step + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat by lia.
      replace (base + step + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat
        by (symmetry; apply odd_subtree_parent_index; apply Prime469.pow2_pos).
      exact Hbound.
    }
    assert (Hbase_step_nat : ((base + step)%nat < len)%nat).
    {
      rewrite Prime469.pow2_succ in Hbound.
      pose proof (prime469_parent_bound_ge_base_step k base step) as Hnat.
      lia.
    }
    assert (Hbase_step : (Z.of_nat (base + step) < Uint63.wB)%Z).
    {
      apply nat_lt_len_lt_wB with len; assumption.
    }
    assert (Hstep2_nat : (step2 < len)%nat).
    {
      subst step2.
      rewrite Prime469.pow2_succ in Hbound.
      eapply Nat.le_lt_trans.
      - apply prime469_parent_bound_ge_step2.
      - exact Hbound.
    }
    assert (Hstep2_bound : (Z.of_nat step2 < Uint63.wB)%Z).
    {
      apply nat_lt_len_lt_wB with len; assumption.
    }
    assert (Hlen_arr1 : PArray.length arr1 = u63_of_nat len).
    {
      subst arr1.
      rewrite coeff_array_from_packed_trees_length.
      exact Hlen.
    }
    replace (Uint63.add (u63_of_nat base) (u63_of_nat step))
      with (u63_of_nat (base + step)).
    2:{
      symmetry.
      apply u63_of_nat_add.
      exact Hbase_step.
    }
    replace (Uint63.add (u63_of_nat step) (u63_of_nat step))
      with (u63_of_nat step2).
    2:{
      subst step2.
      symmetry.
      apply u63_of_nat_add.
      exact Hstep2_bound.
    }
    assert (Hright_pres :
      PArray.get
        (coeff_array_from_packed_trees k arr1 (u63_of_nat (base + step)) (u63_of_nat step2) r469 r181)
        (u63_of_nat j) =
      PArray.get arr1 (u63_of_nat j)).
    {
      eapply (IH len arr1 ((base + step)%nat) step2 r469 r181 j); try eassumption.
      intros i Hi.
      replace ((base + step) + step2 * i)%nat with (base + step * (2 * i + 1))%nat
        by (subst step2; lia).
      apply Hneq.
      rewrite Prime469.pow2_succ.
      lia.
    }
    unfold arr1, step2 in Hright_pres |- *.
    rewrite Hright_pres.
    subst arr1 step2.
    assert (Hleft_neq :
      forall i, (i < Prime469.pow2 (S (S (S k))))%nat ->
        j <> (base + (step + step) * i)%nat).
    {
      intros i Hi.
      replace (base + (step + step) * i)%nat with (base + step * (2 * i))%nat by lia.
      apply Hneq.
      rewrite Prime469.pow2_succ.
      lia.
    }
    exact (IH len arr base ((step + step)%nat) l469 l181 j
      Hlen HlenB Hj Hbound_left Hleft_neq).
Qed.

Lemma fill_crt_block_get :
  forall len arr base step x469 x181 i,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + 7 * step < len)%nat ->
    (i < 8)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat (base + step * i)) =
    crt_combine_u63
      (Prime469.input_get 3 (Prime469.unpack_tree8 0 x469) i)
      (Prime181.input_get 3 (Prime181.unpack_tree8 0 x181) i).
Proof.
  intros len arr base step x469 x181 i Hstep Hlen HlenB Hrange Hi.
  destruct x469 as [x469_0 x469_1 x469_2 x469_3 x469_4 x469_5 x469_6 x469_7].
  destruct x181 as [x181_0 x181_1 x181_2 x181_3 x181_4 x181_5 x181_6 x181_7].
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (base + step * 0)%nat with base by lia.
    eapply fill_crt_block_get_block_index_0; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 1)) with
      (block_index_4 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 1)%nat with (base + step)%nat by lia.
      apply block_index_4_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_4; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 2)) with
      (block_index_2 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
      apply block_index_2_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_2; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 3)) with
      (block_index_6 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
      apply block_index_6_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_6; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 4)) with
      (block_index_1 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
      apply block_index_1_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_1; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 5)) with
      (block_index_5 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
      apply block_index_5_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_5; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 6)) with
      (block_index_3 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
      apply block_index_3_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_3; eauto.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 7)) with
      (block_index_7 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
      apply block_index_7_nat.
      apply nat_lt_len_lt_wB with len; lia.
    }
    eapply fill_crt_block_get_block_index_7; eauto.
Qed.

Lemma coeff_array_from_packed_trees_get :
  forall k len arr base step x469 x181 i,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (base + step * (Prime469.pow2 (S (S (S k))) - 1) < len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    PArray.get (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat (base + step * i)) =
    crt_combine_u63
      (Prime469.input_get (S (S (S k))) (Prime469.unpack_tree8 k x469) i)
      (Prime181.input_get (S (S (S k))) (Prime181.unpack_tree8 k x181) i).
Proof.
  induction k as [|k IH]; intros len arr base step x469 x181 i Hstep Hlen HlenB Hbound Hi.
  - change (Prime469.pow2 3) with 8%nat in Hbound.
    change (Prime469.pow2 3) with 8%nat in Hi.
    replace (base + step * (8 - 1))%nat with (base + 7 * step)%nat in Hbound by lia.
    eapply fill_crt_block_get; eauto.
  - destruct x469 as [l469 r469], x181 as [l181 r181].
    cbn [coeff_array_from_packed_trees Prime469.unpack_tree8 Prime181.unpack_tree8].
    simpl Prime469.input_get.
    simpl Prime181.input_get.
    set (step2 := (step + step)%nat).
    set (arr1 := coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step2) l469 l181).
    assert (Hbase_step_nat : ((base + step)%nat < len)%nat).
    {
      rewrite Prime469.pow2_succ in Hbound.
      pose proof (prime469_parent_bound_ge_base_step k base step) as Hnat.
      lia.
    }
    assert (Hbase_step : (Z.of_nat (base + step) < Uint63.wB)%Z).
    {
      apply nat_lt_len_lt_wB with len; assumption.
    }
    assert (Hstep2_nat : (step2 < len)%nat).
    {
      subst step2.
      rewrite Prime469.pow2_succ in Hbound.
      eapply Nat.le_lt_trans.
      - apply prime469_parent_bound_ge_step2.
      - exact Hbound.
    }
    assert (Hstep2_bound : (Z.of_nat step2 < Uint63.wB)%Z).
    {
      apply nat_lt_len_lt_wB with len; assumption.
    }
    assert (Hlen_arr1 : PArray.length arr1 = u63_of_nat len).
    {
      subst arr1.
      rewrite coeff_array_from_packed_trees_length.
      exact Hlen.
    }
    destruct (Nat.even i) eqn:Heven.
    + apply Nat.even_spec in Heven.
      destruct Heven as [q Hq].
      subst i.
      rewrite Nat.div2_even.
      replace (Uint63.add (u63_of_nat base) (u63_of_nat step))
        with (u63_of_nat (base + step)).
      2:{
        symmetry.
        apply u63_of_nat_add.
        exact Hbase_step.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step))
        with (u63_of_nat step2).
      2:{
        subst step2.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2_bound.
      }
      assert (Hright_out :
        PArray.get
          (coeff_array_from_packed_trees k arr1 (u63_of_nat (base + step)) (u63_of_nat step2) r469 r181)
          (u63_of_nat (base + step * (2 * q))) =
        PArray.get arr1 (u63_of_nat (base + step * (2 * q)))).
      {
        eapply coeff_array_from_packed_trees_preserve_outside.
        - exact Hlen_arr1.
        - exact HlenB.
        - eapply Nat.le_lt_trans with
            (m := (base +
              step * (Prime469.pow2 (S (S (S (S k)))) - 1))%nat).
          2: exact Hbound.
          assert (Hqbound : (2 * q <= Prime469.pow2 (S (S (S (S k)))) - 1)%nat).
          {
            rewrite Prime469.pow2_succ.
            rewrite Prime469.pow2_succ in Hi.
            lia.
          }
          apply Nat.add_le_mono_l.
          apply Nat.mul_le_mono_nonneg_l; [lia|exact Hqbound].
        - rewrite Prime469.pow2_succ in Hbound.
          replace (base + step + step2 * (Prime469.pow2 (S (S (S k))) - 1))%nat
            with (base + step + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
            by (subst step2; lia).
          replace (base + step + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
            with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat
            by (subst step2; symmetry; apply odd_subtree_parent_index; apply Prime469.pow2_pos).
          exact Hbound.
        - intros j Hj.
          subst step2.
          intro Heq.
          replace (base + step + (step + step) * j)%nat
            with (base + step * (2 * j + 1))%nat in Heq by lia.
          assert (Heq_mul : (step * (2 * q) = step * (2 * j + 1))%nat) by lia.
          apply Nat.mul_cancel_l in Heq_mul; try lia.
      }
      unfold arr1, step2 in Hright_out |- *.
      rewrite Hright_out.
      subst arr1 step2.
      replace (base + step * (2 * q))%nat with (base + (step + step) * q)%nat by lia.
      eapply (IH len arr base ((step + step)%nat) l469 l181 q).
      * lia.
      * exact Hlen.
      * exact HlenB.
      * rewrite Prime469.pow2_succ in Hbound.
        eapply Nat.le_lt_trans with
          (m := (base + step *
            (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
        -- pose proof (prime469_even_subtree_bound_le_parent k base step) as Hnat.
           lia.
        -- exact Hbound.
      * rewrite Prime469.pow2_succ in Hi.
        lia.
    + assert (Hodd : Nat.Odd i).
      {
        apply Nat.odd_spec.
        rewrite <- Nat.negb_even.
        now rewrite Heven.
      }
      destruct Hodd as [q Hq].
      subst i.
      rewrite Nat.div2_odd' by reflexivity.
      subst arr1.
      replace (base + step * (2 * q + 1))%nat with ((base + step) + step2 * q)%nat by (subst step2; lia).
      replace (Uint63.add (u63_of_nat base) (u63_of_nat step))
        with (u63_of_nat (base + step)).
      2:{
        symmetry.
        apply u63_of_nat_add.
        exact Hbase_step.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step))
        with (u63_of_nat step2).
      2:{
        subst step2.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2_bound.
      }
      eapply (IH len
        (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step2) l469 l181)
        ((base + step)%nat) step2 r469 r181 q).
      * subst step2; lia.
      * exact Hlen_arr1.
      * exact HlenB.
      * rewrite Prime469.pow2_succ in Hbound.
        replace ((base + step) + step2 * (Prime469.pow2 (S (S (S k))) - 1))%nat
          with ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
          by (subst step2; lia).
        replace ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
          with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat
          by (subst step2; symmetry; apply odd_subtree_parent_index; apply Prime469.pow2_pos).
        exact Hbound.
      * rewrite Prime469.pow2_succ in Hi.
        lia.
Qed.

Lemma coeff_array_from_packed_trees_make_get :
  forall k len x469 x181 i,
    (Z.of_nat len <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Prime469.pow2 (S (S (S k))) <= len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    PArray.get
      (coeff_array_from_packed_trees k (coeff_array_make len) zero_digit u63_one x469 x181)
      (u63_of_nat i) =
    crt_combine_u63
      (Prime469.input_get (S (S (S k))) (Prime469.unpack_tree8 k x469) i)
      (Prime181.input_get (S (S (S k))) (Prime181.unpack_tree8 k x181) i).
Proof.
  intros k len x469 x181 i Hmax HlenB Hpow Hi.
  unfold zero_digit, u63_one.
  change (Uint63.of_Z 0) with (u63_of_nat 0).
  change (Uint63.of_Z 1) with (u63_of_nat 1).
  replace (u63_of_nat i) with (u63_of_nat ((0 + 1 * i)%nat)).
  2:{ f_equal; lia. }
  eapply coeff_array_from_packed_trees_get.
  - lia.
  - apply coeff_array_make_length.
    exact Hmax.
  - exact HlenB.
  - change (0 + 1 * (Prime469.pow2 (S (S (S k))) - 1) < len)%nat.
    lia.
  - exact Hi.
Qed.
