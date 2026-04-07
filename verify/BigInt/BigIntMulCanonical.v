From Coq Require Import Uint63 ZArith Lia Lists.List Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul BigInt.BigIntMulProof.

Import ListNotations.
Local Open Scope Z_scope.

Lemma canonical_zero_digit : canonical_digit zero_digit.
Proof.
  unfold canonical_digit, zero_digit, digit_base_z.
  vm_compute.
  split.
  - discriminate.
  - reflexivity.
Qed.

Lemma canonical_zero_limb8 : canonical_limb8 zero_limb8.
Proof.
  repeat split; apply canonical_zero_digit.
Qed.

Lemma prime469_modulus_z :
  Prime469.modulus_z = 469762049%Z.
Proof.
  unfold Prime469.modulus_z, Prime469Cfg.modulus.
  vm_compute.
  reflexivity.
Qed.

Lemma prime181_modulus_z :
  Prime181.modulus_z = 1811939329%Z.
Proof.
  unfold Prime181.modulus_z, Prime181Cfg.modulus.
  vm_compute.
  reflexivity.
Qed.

Lemma canonical_digit_prime469 :
  forall x,
    canonical_digit x ->
    Prime469.canonical x.
Proof.
  intros x Hx.
  unfold canonical_digit, Prime469.canonical, Prime469.value in *.
  rewrite prime469_modulus_z.
  cbv [digit_base_z] in Hx.
  lia.
Qed.

Lemma canonical_digit_prime181 :
  forall x,
    canonical_digit x ->
    Prime181.canonical x.
Proof.
  intros x Hx.
  unfold canonical_digit, Prime181.canonical, Prime181.value in *.
  rewrite prime181_modulus_z.
  cbv [digit_base_z] in Hx.
  lia.
Qed.

Lemma Forall_nth_default :
  forall (A : Type) (P : A -> Prop) xs d n,
    Forall P xs ->
    P d ->
    P (nth n xs d).
Proof.
  intros A P xs.
  induction xs as [|x xs IH]; intros d n Hxs Hd.
  - destruct n; exact Hd.
  - inversion Hxs as [|x' xs' Hx Hrest]; subst.
    destruct n as [|n].
    + exact Hx.
    + apply IH; assumption.
Qed.

Lemma canonical_limb8_get_nat :
  forall x n,
    canonical_limb8 x ->
    (n < 8)%nat ->
    canonical_digit (limb8_get_nat x n).
Proof.
  intros x n Hx Hn.
  destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; try lia; assumption.
Qed.

Lemma canonical_bigint_nth_digit :
  forall x i,
    canonical_bigint x ->
    canonical_digit (nth i (bigint_digits_u63_flat x) zero_digit).
Proof.
  intros x i Hx.
  rewrite nth_bigint_digits_u63_flat.
  apply canonical_limb8_get_nat.
  - apply Forall_nth_default with (d := zero_limb8); try assumption.
    apply canonical_zero_limb8.
  - apply Nat.mod_upper_bound.
    lia.
Qed.

Lemma canonical_tree_of_input_get469 :
  forall (n : nat) (t : tree Prime469.int n),
    (forall i, (i < Prime469.pow2 n)%nat -> Prime469.canonical (Prime469.input_get n t i)) ->
    Prime469.canonical_tree n t.
Proof.
  induction n as [|n IH]; intros t Ht.
  - exact (Ht 0%nat (Nat.lt_0_succ 0)).
  - destruct t as [l r].
    split.
    + apply IH.
      intros i Hi.
      specialize (Ht (2 * i)%nat).
      rewrite Prime469.pow2_succ in Ht.
      replace (Prime469.input_get (S n) (l, r) (2 * i))
        with (Prime469.input_get n l i) in Ht.
      2:{
        cbn [Prime469.input_get].
        replace (Nat.even (2 * i)) with true by
          (rewrite Nat.even_mul; simpl; reflexivity).
        rewrite Nat.div2_even.
        reflexivity.
      }
      apply Ht.
      lia.
    + apply IH.
      intros i Hi.
      specialize (Ht (2 * i + 1)%nat).
      rewrite Prime469.pow2_succ in Ht.
      replace (Prime469.input_get (S n) (l, r) (2 * i + 1))
        with (Prime469.input_get n r i) in Ht.
      2:{
        cbn [Prime469.input_get].
        rewrite Nat.even_odd.
        rewrite Nat.div2_odd'.
        reflexivity.
      }
      apply Ht.
      lia.
Qed.

Lemma canonical_tree_of_input_get181 :
  forall (n : nat) (t : tree Prime181.int n),
    (forall i, (i < Prime181.pow2 n)%nat -> Prime181.canonical (Prime181.input_get n t i)) ->
    Prime181.canonical_tree n t.
Proof.
  induction n as [|n IH]; intros t Ht.
  - exact (Ht 0%nat (Nat.lt_0_succ 0)).
  - destruct t as [l r].
    split.
    + apply IH.
      intros i Hi.
      specialize (Ht (2 * i)%nat).
      rewrite Prime181.pow2_succ in Ht.
      replace (Prime181.input_get (S n) (l, r) (2 * i))
        with (Prime181.input_get n l i) in Ht.
      2:{
        cbn [Prime181.input_get].
        replace (Nat.even (2 * i)) with true by
          (rewrite Nat.even_mul; simpl; reflexivity).
        rewrite Nat.div2_even.
        reflexivity.
      }
      apply Ht.
      lia.
    + apply IH.
      intros i Hi.
      specialize (Ht (2 * i + 1)%nat).
      rewrite Prime181.pow2_succ in Ht.
      replace (Prime181.input_get (S n) (l, r) (2 * i + 1))
        with (Prime181.input_get n r i) in Ht.
      2:{
        cbn [Prime181.input_get].
        rewrite Nat.even_odd.
        rewrite Nat.div2_odd'.
        reflexivity.
      }
      apply Ht.
      lia.
Qed.

Lemma build_tree469_canonical :
  forall k x,
    (k <= supported_max_block_log)%nat ->
    canonical_bigint x ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime469.canonical_tree (S (S (S k)))
      (Prime469.unpack_tree8 k (build_tree469 k x)).
Proof.
  intros k x Hk Hx Hlen.
  apply canonical_tree_of_input_get469.
  intros i Hi.
  rewrite build_tree469_input_get by assumption.
  apply canonical_digit_prime469.
  apply canonical_bigint_nth_digit.
  exact Hx.
Qed.

Lemma build_tree181_canonical :
  forall k x,
    (k <= supported_max_block_log)%nat ->
    canonical_bigint x ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime181.canonical_tree (S (S (S k)))
      (Prime181.unpack_tree8 k (build_tree181 k x)).
Proof.
  intros k x Hk Hx Hlen.
  apply canonical_tree_of_input_get181.
  intros i Hi.
  rewrite build_tree181_input_get by assumption.
  apply canonical_digit_prime181.
  apply canonical_bigint_nth_digit.
  exact Hx.
Qed.
