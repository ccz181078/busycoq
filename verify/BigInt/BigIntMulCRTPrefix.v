From Coq Require Import Uint63 ZArith Lia Lists.List Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof
  BigInt.BigIntMulCRT.

Import ListNotations.
Local Open Scope Z_scope.

Lemma nat_le_wB_of_bound :
  forall n bound,
    (n <= bound)%nat ->
    (Z.of_nat bound < Uint63.wB)%Z ->
    (Z.of_nat n < Uint63.wB)%Z.
Proof.
  intros n bound Hn Hbound.
  lia.
Qed.

Lemma fill_crt_block_get_prefix :
  forall len arr base step x469 x181 i,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Z.of_nat (base + 7 * step) < Uint63.wB)%Z ->
    (base + step * i < len)%nat ->
    (i < 8)%nat ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat (base + step * i)) =
    crt_combine_u63
      (Prime469.input_get 3 (Prime469.unpack_tree8 0 x469) i)
      (Prime181.input_get 3 (Prime181.unpack_tree8 0 x181) i).
Proof.
  intros len arr base step x469 x181 i Hstep Hlen HlenB HboundW Htarget Hi.
  destruct x469 as [x469_0 x469_1 x469_2 x469_3 x469_4 x469_5 x469_6 x469_7].
  destruct x181 as [x181_0 x181_1 x181_2 x181_3 x181_4 x181_5 x181_6 x181_7].
  assert (Hidx0w : (Z.of_nat (base + step * 0) < Uint63.wB)%Z) by (simpl; lia).
  assert (Hidx1w : (Z.of_nat (base + step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx2w : (Z.of_nat (base + 2 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx3w : (Z.of_nat (base + 3 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx4w : (Z.of_nat (base + 4 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx5w : (Z.of_nat (base + 5 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx6w : (Z.of_nat (base + 6 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx7w : (Z.of_nat (base + 7 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hblk1 :
    block_index_1 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 4 * step)).
  { apply block_index_1_nat. lia. }
  assert (Hblk2 :
    block_index_2 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 2 * step)).
  { apply block_index_2_nat. lia. }
  assert (Hblk3 :
    block_index_3 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 6 * step)).
  { apply block_index_3_nat. lia. }
  assert (Hblk4 :
    block_index_4 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + step)).
  { apply block_index_4_nat. lia. }
  assert (Hblk5 :
    block_index_5 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 5 * step)).
  { apply block_index_5_nat. lia. }
  assert (Hblk6 :
    block_index_6 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 3 * step)).
  { apply block_index_6_nat. lia. }
  assert (Hblk7 :
    block_index_7 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 7 * step)).
  { apply block_index_7_nat. lia. }
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (base + step * 0)%nat with base by lia.
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk5. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk4. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk3. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 1)) with
      (block_index_4 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 1)%nat with (base + step)%nat by lia.
      rewrite Hblk4.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk4. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6, Hblk4. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk5, Hblk4. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk4.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 2)) with
      (block_index_2 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
      rewrite Hblk2.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6, Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk5, Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk4, Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk3, Hblk2. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk2.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 3)) with
      (block_index_6 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
      rewrite Hblk6.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk6. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk6.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 4)) with
      (block_index_1 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
      rewrite Hblk1.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk5, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk4, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk3, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk2, Hblk1. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk1.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 5)) with
      (block_index_5 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
      rewrite Hblk5.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk5. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6, Hblk5. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk5.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 6)) with
      (block_index_3 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
      rewrite Hblk3.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk7, Hblk3. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk6, Hblk3. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk5, Hblk3. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_other.
    2:{ rewrite Hblk4, Hblk3. eapply u63_of_nat_neq; eauto; lia. }
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk3.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
  - cbn [Prime469.unpack_tree8 Prime181.unpack_tree8 Prime469.input_get Prime181.input_get].
    replace (u63_of_nat (base + step * 7)) with
      (block_index_7 (u63_of_nat base) (u63_of_nat step)).
    2:{
      replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
      rewrite Hblk7.
      reflexivity.
    }
    unfold fill_crt_block.
    rewrite coeff_array_set_if_in_bounds_same.
    2:{
      rewrite Hblk7.
      repeat rewrite coeff_array_set_if_in_bounds_length.
      rewrite Hlen.
      apply u63_of_nat_index_ltb_length.
      lia.
      exact HlenB.
    }
    reflexivity.
Qed.

Lemma fill_crt_block_preserve_outside_prefix :
  forall len arr base step x469 x181 j,
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (j < len)%nat ->
    (Z.of_nat (base + 7 * step) < Uint63.wB)%Z ->
    (forall i, (i < 8)%nat -> j <> (base + step * i)%nat) ->
    PArray.get (fill_crt_block arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat j) =
    PArray.get arr (u63_of_nat j).
Proof.
  intros len arr base step x469 x181 j Hlen HlenB Hj HboundW Hneq.
  assert (Hjw : (Z.of_nat j < Uint63.wB)%Z).
  { apply nat_lt_len_lt_wB with len; assumption. }
  assert (Hidx0w : (Z.of_nat base < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx1w : (Z.of_nat (base + step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx2w : (Z.of_nat (base + 2 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx3w : (Z.of_nat (base + 3 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx4w : (Z.of_nat (base + 4 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx5w : (Z.of_nat (base + 5 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx6w : (Z.of_nat (base + 6 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hidx7w : (Z.of_nat (base + 7 * step) < Uint63.wB)%Z).
  { apply nat_le_wB_of_bound with (bound := (base + 7 * step)%nat); lia. }
  assert (Hblk1 :
    block_index_1 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 4 * step)).
  { apply block_index_1_nat. lia. }
  assert (Hblk2 :
    block_index_2 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 2 * step)).
  { apply block_index_2_nat. lia. }
  assert (Hblk3 :
    block_index_3 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 6 * step)).
  { apply block_index_3_nat. lia. }
  assert (Hblk4 :
    block_index_4 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + step)).
  { apply block_index_4_nat. lia. }
  assert (Hblk5 :
    block_index_5 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 5 * step)).
  { apply block_index_5_nat. lia. }
  assert (Hblk6 :
    block_index_6 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 3 * step)).
  { apply block_index_6_nat. lia. }
  assert (Hblk7 :
    block_index_7 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 7 * step)).
  { apply block_index_7_nat. lia. }
  unfold fill_crt_block.
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk7.
    apply u63_of_nat_neq.
    - exact Hidx7w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 7%nat); [lia|].
    replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk6.
    apply u63_of_nat_neq.
    - exact Hidx3w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 3%nat); [lia|].
    replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk5.
    apply u63_of_nat_neq.
    - exact Hidx5w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 5%nat); [lia|].
    replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk4.
    apply u63_of_nat_neq.
    - exact Hidx1w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 1%nat); [lia|].
    replace (base + step * 1)%nat with (base + step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk3.
    apply u63_of_nat_neq.
    - exact Hidx6w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 6%nat); [lia|].
    replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk2.
    apply u63_of_nat_neq.
    - exact Hidx2w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 2%nat); [lia|].
    replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    rewrite Hblk1.
    apply u63_of_nat_neq.
    - exact Hidx4w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 4%nat); [lia|].
    replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
    symmetry.
    exact Heq.
  }
  rewrite coeff_array_set_if_in_bounds_other.
  2:{
    apply u63_of_nat_neq.
    - exact Hidx0w.
    - exact Hjw.
    - intro Heq.
    apply (Hneq 0%nat); [lia|].
    replace (base + step * 0)%nat with base by lia.
    symmetry.
    exact Heq.
  }
  reflexivity.
Qed.

Lemma coeff_array_from_packed_trees_preserve_outside_prefix :
  forall k len arr base step x469 x181 j,
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (j < len)%nat ->
    (Z.of_nat (base + step * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z ->
    (forall i, (i < Prime469.pow2 (S (S (S k))))%nat -> j <> (base + step * i)%nat) ->
    PArray.get (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat j) =
    PArray.get arr (u63_of_nat j).
Proof.
  induction k as [|k IH]; intros len arr base step x469 x181 j Hlen HlenB Hj HboundW Hneq.
  - change (Prime469.pow2 3) with 8%nat in HboundW.
    replace (base + step * (8 - 1))%nat with (base + 7 * step)%nat in HboundW by lia.
    eapply fill_crt_block_preserve_outside_prefix; eauto.
  - destruct x469 as [l469 r469], x181 as [l181 r181].
    cbn [coeff_array_from_packed_trees].
    set (step2 := (step + step)%nat).
    set (arr1 := coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step2) l469 l181).
    rewrite Prime469.pow2_succ in HboundW.
    assert (Hbound_left :
      (Z.of_nat (base + step2 * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z).
    {
      subst step2.
      replace ((step + step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with ((2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat by lia.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_even_subtree_bound_le_parent k base step) as Hnat.
        lia.
      - exact HboundW.
    }
    assert (Hbound_right :
      (Z.of_nat ((base + step) + step2 * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z).
    {
      subst step2.
      replace ((base + step) + (step + step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat by lia.
      replace ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat
        by (symmetry; apply odd_subtree_parent_index; apply Prime469.pow2_pos).
      exact HboundW.
    }
    assert (Hbase_step_bound : (Z.of_nat (base + step) < Uint63.wB)%Z).
    {
      subst step2.
      replace (step + step)%nat with (2 * step)%nat by lia.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_parent_bound_ge_base_step k base step) as Hnat.
        lia.
      - exact HboundW.
    }
    assert (Hstep2_bound : (Z.of_nat step2 < Uint63.wB)%Z).
    {
      subst step2.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_parent_bound_ge_step2 k base step) as Hnat.
        lia.
      - exact HboundW.
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
      exact Hbase_step_bound.
    }
    replace (Uint63.add (u63_of_nat step) (u63_of_nat step))
      with (u63_of_nat step2).
    2:{
      subst step2.
      symmetry.
      apply u63_of_nat_add.
      exact Hstep2_bound.
    }
    assert (Hleft_pres :
      PArray.get arr1 (u63_of_nat j) = PArray.get arr (u63_of_nat j)).
    {
      subst arr1 step2.
      eapply (IH len arr base ((step + step)%nat) l469 l181 j).
      + exact Hlen.
      + exact HlenB.
      + exact Hj.
      + exact Hbound_left.
      + intros i Hi.
        replace (base + (step + step) * i)%nat with (base + step * (2 * i))%nat by lia.
        apply Hneq.
        rewrite Prime469.pow2_succ.
        lia.
    }
    rewrite <- Hleft_pres.
    subst arr1 step2.
    eapply (IH len
      (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat (step + step)) l469 l181)
      (base + step)%nat ((step + step)%nat) r469 r181 j).
    + exact Hlen_arr1.
    + exact HlenB.
    + exact Hj.
    + exact Hbound_right.
    + intros i Hi.
      replace ((base + step) + (step + step) * i)%nat
        with (base + step * (2 * i + 1))%nat by lia.
      apply Hneq.
      rewrite Prime469.pow2_succ.
      lia.
Qed.

Lemma coeff_array_from_packed_trees_get_prefix :
  forall k len arr base step x469 x181 i,
    (0 < step)%nat ->
    PArray.length arr = u63_of_nat len ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (Z.of_nat (base + step * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z ->
    (base + step * i < len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    PArray.get (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step) x469 x181)
      (u63_of_nat (base + step * i)) =
    crt_combine_u63
      (Prime469.input_get (S (S (S k))) (Prime469.unpack_tree8 k x469) i)
      (Prime181.input_get (S (S (S k))) (Prime181.unpack_tree8 k x181) i).
Proof.
  induction k as [|k IH]; intros len arr base step x469 x181 i Hstep Hlen HlenB HboundW Htarget Hi.
  - change (Prime469.pow2 3) with 8%nat in HboundW.
    change (Prime469.pow2 3) with 8%nat in Hi.
    replace (base + step * (8 - 1))%nat with (base + 7 * step)%nat in HboundW by lia.
    eapply fill_crt_block_get_prefix; eauto.
  - destruct x469 as [l469 r469], x181 as [l181 r181].
    cbn [coeff_array_from_packed_trees Prime469.unpack_tree8 Prime181.unpack_tree8].
    simpl Prime469.input_get.
    simpl Prime181.input_get.
    set (step2 := (step + step)%nat).
    set (arr1 := coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat step2) l469 l181).
    rewrite Prime469.pow2_succ in HboundW.
    assert (Hbound_left :
      (Z.of_nat (base + step2 * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z).
    {
      subst step2.
      replace ((step + step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with ((2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat by lia.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_even_subtree_bound_le_parent k base step) as Hnat.
        lia.
      - exact HboundW.
    }
    assert (Hbound_right :
      (Z.of_nat ((base + step) + step2 * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z).
    {
      subst step2.
      replace ((base + step) + (step + step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat by lia.
      replace ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
        with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat
        by (symmetry; apply odd_subtree_parent_index; apply Prime469.pow2_pos).
      exact HboundW.
    }
    assert (Hbase_step_bound : (Z.of_nat (base + step) < Uint63.wB)%Z).
    {
      subst step2.
      replace (step + step)%nat with (2 * step)%nat by lia.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_parent_bound_ge_base_step k base step) as Hnat.
        lia.
      - exact HboundW.
    }
    assert (Hstep2_bound : (Z.of_nat step2 < Uint63.wB)%Z).
    {
      subst step2.
      replace (step + step)%nat with (2 * step)%nat by lia.
      apply nat_le_wB_of_bound with
        (bound := (base + step *
          (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat).
      - pose proof (prime469_parent_bound_ge_step2 k base step) as Hnat.
        lia.
      - exact HboundW.
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
        exact Hbase_step_bound.
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
          (u63_of_nat (base + step * (2 * q))) =
        PArray.get arr1 (u63_of_nat (base + step * (2 * q)))).
      {
        eapply coeff_array_from_packed_trees_preserve_outside_prefix.
        - exact Hlen_arr1.
        - exact HlenB.
        - exact Htarget.
        - exact Hbound_right.
        - intros j Hj.
          replace ((base + step) + step2 * j)%nat
            with (base + step * (2 * j + 1))%nat by (subst step2; lia).
          intro Heq.
          assert (Heq_mul : (step * (2 * q) = step * (2 * j + 1))%nat) by lia.
          apply Nat.mul_cancel_l in Heq_mul; try lia.
      }
      subst arr1 step2.
      rewrite Hright_pres.
      replace (base + step * (2 * q))%nat with (base + (step + step) * q)%nat by lia.
      eapply (IH len arr base ((step + step)%nat) l469 l181 q).
      * lia.
      * exact Hlen.
      * exact HlenB.
      * exact Hbound_left.
      * lia.
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
      replace (Uint63.add (u63_of_nat base) (u63_of_nat step))
        with (u63_of_nat (base + step)).
      2:{
        symmetry.
        apply u63_of_nat_add.
        exact Hbase_step_bound.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step))
        with (u63_of_nat step2).
      2:{
        subst step2.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2_bound.
      }
      subst arr1 step2.
      replace (base + step * (2 * q + 1))%nat with ((base + step) + (step + step) * q)%nat by lia.
      eapply (IH len
        (coeff_array_from_packed_trees k arr (u63_of_nat base) (u63_of_nat (step + step)) l469 l181)
        (base + step)%nat ((step + step)%nat) r469 r181 q).
      * lia.
      * exact Hlen_arr1.
      * exact HlenB.
      * exact Hbound_right.
      * lia.
      * rewrite Prime469.pow2_succ in Hi.
        lia.
Qed.

Lemma coeff_array_from_packed_trees_make_get_prefix :
  forall k len x469 x181 i,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat len <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat len < Uint63.wB)%Z ->
    (i < len)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    PArray.get
      (coeff_array_from_packed_trees k (coeff_array_make len) zero_digit u63_one x469 x181)
      (u63_of_nat i) =
    crt_combine_u63
      (Prime469.input_get (S (S (S k))) (Prime469.unpack_tree8 k x469) i)
      (Prime181.input_get (S (S (S k))) (Prime181.unpack_tree8 k x181) i).
Proof.
  intros k len x469 x181 i Hk Hmax HlenB HiLen Hi.
  unfold zero_digit, u63_one.
  change (Uint63.of_Z 0) with (u63_of_nat 0).
  change (Uint63.of_Z 1) with (u63_of_nat 1).
  replace (u63_of_nat i) with (u63_of_nat ((0 + 1 * i)%nat)).
  2:{ f_equal; lia. }
  eapply coeff_array_from_packed_trees_get_prefix.
  - lia.
  - apply coeff_array_make_length.
    exact Hmax.
  - exact HlenB.
  - replace (0 + 1 * (Prime469.pow2 (S (S (S k))) - 1))%nat
      with (Prime469.pow2 (S (S (S k))) - 1)%nat by lia.
    apply prime469_transform_bound.
    exact Hk.
  - replace (0 + 1 * i)%nat with i by lia.
    exact HiLen.
  - exact Hi.
Qed.
