From Coq Require Import Uint63 ZArith Lia Lists.List Arith.PeanoNat Array.PArray.
Require Import BigInt.NTTTree BigInt.NTTConcrete BigInt.BigIntMul.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_base8_z : Z := digit_base_z ^ 8.

Definition canonical_digit (x : Uint63.int) : Prop :=
  (0 <= Uint63.to_Z x < digit_base_z)%Z.

Definition canonical_limb8 (x : limb8) : Prop :=
  canonical_digit (d0 x) /\
  canonical_digit (d1 x) /\
  canonical_digit (d2 x) /\
  canonical_digit (d3 x) /\
  canonical_digit (d4 x) /\
  canonical_digit (d5 x) /\
  canonical_digit (d6 x) /\
  canonical_digit (d7 x).

Definition canonical_bigint (x : bigint) : Prop :=
  Forall canonical_limb8 x.

Definition limb8_value (x : limb8) : Z :=
  digits_value (limb8_digits_z x).

Fixpoint bigint_value_blocks (fuel : nat) (x : bigint) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      match x with
      | [] => 0
      | b :: bs => limb8_value b + digit_base8_z * bigint_value_blocks fuel' bs
      end
  end.

Fixpoint zsum_nat (n : nat) (f : nat -> Z) : Z :=
  match n with
  | O => 0
  | S m => zsum_nat m f + f m
  end.

Fixpoint bigint_digits_u63_flat (x : bigint) : list Uint63.int :=
  match x with
  | [] => []
  | b :: bs => limb8_digits_u63 b ++ bigint_digits_u63_flat bs
  end.

Definition bigint_digits_z_flat (x : bigint) : list Z :=
  map Uint63.to_Z (bigint_digits_u63_flat x).

Fixpoint digits_value_base (base : Z) (digits : list Z) : Z :=
  match digits with
  | [] => 0
  | d :: ds => d + base * digits_value_base base ds
  end.

Lemma digits_value_base_app :
  forall base xs ys,
    digits_value_base base (xs ++ ys) =
    digits_value_base base xs +
    (base ^ Z.of_nat (List.length xs)) * digits_value_base base ys.
Proof.
  intros base xs.
  revert base.
  induction xs as [|x xs IH]; intros base ys.
  - simpl.
    change (base ^ 0) with 1%Z.
    destruct (digits_value_base base ys); reflexivity.
  - simpl.
    rewrite IH.
    rewrite Z.pow_pos_fold.
    rewrite Zpos_P_of_succ_nat.
    change (Z.succ (Z.of_nat (List.length xs)))
      with (Z.of_nat (List.length xs) + 1).
    rewrite Z.pow_add_r by lia.
    ring.
Qed.

Lemma digits_value_eq_base :
  forall xs,
    digits_value xs = digits_value_base digit_base_z xs.
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma digits_value_base_range :
  forall base digits,
    (1 < base)%Z ->
    Forall (fun d => (0 <= d < base)%Z) digits ->
    (0 <= digits_value_base base digits < base ^ Z.of_nat (List.length digits))%Z.
Proof.
  intros base digits Hbase.
  induction digits as [|d ds IH]; intros Hdigits.
  - simpl.
    replace (Z.of_nat 0) with 0%Z by reflexivity.
    simpl.
    lia.
  - inversion Hdigits as [|d' ds' Hd Hds]; subst.
    simpl.
    specialize (IH Hds).
    destruct IH as [IH0 IH1].
    rewrite Z.pow_pos_fold.
    rewrite Zpos_P_of_succ_nat.
    change (Z.succ (Z.of_nat (List.length ds)))
      with (Z.of_nat (List.length ds) + 1).
    rewrite Z.pow_add_r by lia.
    split.
    + nia.
    + assert (0 <= base ^ Z.of_nat (List.length ds))%Z.
      {
        apply Z.pow_nonneg.
        lia.
      }
      nia.
Qed.

Lemma limb8_digits_u63_length :
  forall x, List.length (limb8_digits_u63 x) = 8%nat.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7].
  reflexivity.
Qed.

Lemma limb8_digits_z_eq_map :
  forall x,
    limb8_digits_z x = map Uint63.to_Z (limb8_digits_u63 x).
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7].
  reflexivity.
Qed.

Lemma limb8_digits_z_length :
  forall x, List.length (limb8_digits_z x) = 8%nat.
Proof.
  intros x.
  rewrite limb8_digits_z_eq_map.
  rewrite length_map.
  apply limb8_digits_u63_length.
Qed.

Lemma bigint_digits_u63_rev_eq_flat :
  forall x acc,
    bigint_digits_u63_rev x acc =
    rev_append (bigint_digits_u63_flat x) acc.
Proof.
  induction x as [|b bs IH]; intros acc.
  - reflexivity.
  - simpl bigint_digits_u63_rev.
    simpl bigint_digits_u63_flat.
    rewrite IH.
    rewrite !rev_append_rev.
    rewrite rev_app_distr.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma bigint_digits_u63_eq_flat :
  forall x,
    bigint_digits_u63 x = bigint_digits_u63_flat x.
Proof.
  intros x.
  unfold bigint_digits_u63.
  rewrite bigint_digits_u63_rev_eq_flat.
  rewrite rev_append_rev.
  rewrite app_nil_r.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma bigint_digits_z_eq_flat :
  forall x,
    bigint_digits_z x = bigint_digits_z_flat x.
Proof.
  induction x as [|b bs IH].
  - reflexivity.
  - simpl.
    rewrite limb8_digits_z_eq_map.
    unfold bigint_digits_z_flat in *.
    simpl.
    rewrite map_app.
    rewrite IH.
    reflexivity.
Qed.

Lemma digits_value_app :
  forall xs ys,
    digits_value (xs ++ ys) =
    digits_value xs + (digit_base_z ^ Z.of_nat (List.length xs)) * digits_value ys.
Proof.
  intros xs ys.
  repeat rewrite digits_value_eq_base.
  exact (digits_value_base_app digit_base_z xs ys).
Qed.

Lemma limb8_value_range :
  forall x,
    canonical_limb8 x ->
    (0 <= limb8_value x < digit_base8_z)%Z.
Proof.
  intros x Hx.
  destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct Hx as [Hx0 [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 [Hx6 Hx7]]]]]]].
  unfold limb8_value.
  rewrite limb8_digits_z_eq_map.
  rewrite digits_value_eq_base.
  unfold digit_base8_z.
  apply digits_value_base_range.
  - cbv [digit_base_z].
    lia.
  - unfold canonical_digit in *.
    simpl in *.
    constructor; [exact Hx0|].
    constructor; [exact Hx1|].
    constructor; [exact Hx2|].
    constructor; [exact Hx3|].
    constructor; [exact Hx4|].
    constructor; [exact Hx5|].
    constructor; [exact Hx6|].
    constructor; [exact Hx7|].
    constructor.
Qed.

Lemma bigint_value_cons :
  forall b bs,
    bigint_value (b :: bs) = limb8_value b + digit_base8_z * bigint_value bs.
Proof.
  intros b bs.
  unfold bigint_value.
  simpl.
  rewrite digits_value_app.
  rewrite limb8_digits_z_length.
  change (Z.of_nat 8) with 8%Z.
  reflexivity.
Qed.

Lemma bigint_value_eq_blocks :
  forall x,
    bigint_value x = bigint_value_blocks (List.length x) x.
Proof.
  induction x as [|b bs IH].
  - reflexivity.
  - simpl List.length.
    simpl bigint_value_blocks.
    rewrite bigint_value_cons.
    rewrite IH.
    reflexivity.
Qed.

Lemma bigint_value_blocks_ge :
  forall fuel x,
    (List.length x <= fuel)%nat ->
    bigint_value_blocks fuel x = bigint_value x.
Proof.
  induction fuel as [|fuel IH]; intros x Hlen.
  - destruct x as [|b bs].
    + reflexivity.
    + simpl in Hlen.
      lia.
  - destruct x as [|b bs].
    + reflexivity.
    + simpl in Hlen.
      simpl bigint_value_blocks.
      rewrite bigint_value_cons.
      replace (bigint_value_blocks fuel bs) with (bigint_value bs).
      * reflexivity.
      * symmetry. apply IH. lia.
Qed.

Lemma u63_of_nat_small :
  forall n,
    (Z.of_nat n < Uint63.wB)%Z ->
    Uint63.to_Z (u63_of_nat n) = Z.of_nat n.
Proof.
  intros n Hn.
  unfold u63_of_nat.
  rewrite Uint63.of_Z_spec.
  apply Z.mod_small.
  split; [lia|assumption].
Qed.

Lemma u63_of_nat_ltb :
  forall m n,
    (m < n)%nat ->
    (Z.of_nat n < Uint63.wB)%Z ->
    (u63_of_nat m <? u63_of_nat n)%uint63 = true.
Proof.
  intros m n Hmn Hn.
  apply Uint63.ltb_spec.
  rewrite !u63_of_nat_small; lia.
Qed.

Lemma u63_of_nat_leb :
  forall m n,
    (m <= n)%nat ->
    (Z.of_nat n < Uint63.wB)%Z ->
    (u63_of_nat m ≤? u63_of_nat n)%uint63 = true.
Proof.
  intros m n Hmn Hn.
  apply Uint63.leb_spec.
  rewrite !u63_of_nat_small; lia.
Qed.

Lemma u63_of_nat_inj :
  forall m n,
    (Z.of_nat m < Uint63.wB)%Z ->
    (Z.of_nat n < Uint63.wB)%Z ->
    u63_of_nat m = u63_of_nat n ->
    m = n.
Proof.
  intros m n Hm Hn Heq.
  apply Nat2Z.inj.
  rewrite <- !u63_of_nat_small by assumption.
  now apply f_equal with (f := Uint63.to_Z) in Heq.
Qed.

Lemma u63_of_nat_succ :
  forall n,
    (Z.of_nat (S n) < Uint63.wB)%Z ->
    (u63_of_nat n + u63_one)%uint63 = u63_of_nat (S n).
Proof.
  intros n Hn.
  assert (Hz :
    Uint63.to_Z ((u63_of_nat n + u63_one)%uint63) =
    Uint63.to_Z (u63_of_nat (S n))).
  {
    rewrite Uint63.add_spec.
    rewrite u63_of_nat_small by lia.
    change (Uint63.to_Z u63_one) with 1%Z.
    rewrite u63_of_nat_small by exact Hn.
    rewrite Z.mod_small by lia.
    lia.
  }
  apply (f_equal Uint63.of_Z) in Hz.
  rewrite !Uint63.of_to_Z in Hz.
  exact Hz.
Qed.

Lemma limb_array_of_bigint_aux_length :
  forall idx xs acc,
    PArray.length (limb_array_of_bigint_aux idx xs acc) = PArray.length acc.
Proof.
  intros idx xs.
  revert idx.
  induction xs as [|x xs IH]; intros idx acc.
  - reflexivity.
  - simpl.
    rewrite IH.
    apply PArray.length_set.
Qed.

Lemma limb_array_of_bigint_aux_default :
  forall idx xs acc,
    PArray.default (limb_array_of_bigint_aux idx xs acc) = PArray.default acc.
Proof.
  intros idx xs.
  revert idx.
  induction xs as [|x xs IH]; intros idx acc.
  - reflexivity.
  - simpl.
    rewrite IH.
    apply PArray.default_set.
Qed.

Lemma limb_array_of_bigint_length :
  forall xs,
    (Z.of_nat (List.length xs) <= Uint63.to_Z PArray.max_length)%Z ->
    PArray.length (limb_array_of_bigint xs) = u63_of_nat (List.length xs).
Proof.
  intros xs Hxs.
  unfold limb_array_of_bigint.
  rewrite limb_array_of_bigint_aux_length.
  rewrite PArray.length_make.
  unfold u63_of_nat.
  assert (Hleb : (Uint63.of_Z (Z.of_nat (List.length xs)) ≤? PArray.max_length)%uint63 = true).
  {
    apply Uint63.leb_spec.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    - exact Hxs.
    - split.
      + lia.
      + eapply Z.le_lt_trans; [apply Hxs|].
        apply Uint63.to_Z_bounded.
  }
  rewrite Hleb.
  reflexivity.
Qed.

Definition limb8_get_nat (x : limb8) (n : nat) : Uint63.int :=
  match n with
  | O => d0 x
  | 1%nat => d1 x
  | 2%nat => d2 x
  | 3%nat => d3 x
  | 4%nat => d4 x
  | 5%nat => d5 x
  | 6%nat => d6 x
  | 7%nat => d7 x
  | _ => zero_digit
  end.

Lemma limb8_get_nat_eq :
  forall x n,
    (n < 8)%nat ->
    limb8_get x (u63_of_nat n) = limb8_get_nat x n.
Proof.
  intros x n Hn.
  destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; try lia; reflexivity.
Qed.

Lemma limb8_digits_u63_nth :
  forall x n,
    nth n (limb8_digits_u63 x) zero_digit = limb8_get_nat x n.
Proof.
  intros x n.
  destruct x as [x0 x1 x2 x3 x4 x5 x6 x7].
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; simpl; try reflexivity.
  destruct n; reflexivity.
Qed.

Lemma limb8_get_nat_zero_limb8 :
  forall n,
    limb8_get_nat zero_limb8 n = zero_digit.
Proof.
  intros n.
  destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; reflexivity.
Qed.

Lemma nth_bigint_digits_u63_flat :
  forall xs j,
    nth j (bigint_digits_u63_flat xs) zero_digit =
    limb8_get_nat (nth (Nat.div j 8) xs zero_limb8) (Nat.modulo j 8).
  Proof.
  induction xs as [|x xs IH]; intros j.
  - cbn [bigint_digits_u63_flat].
    replace (nth j [] zero_digit) with zero_digit by (destruct j; reflexivity).
    replace (nth (Nat.div j 8) [] zero_limb8) with zero_limb8
      by (destruct (Nat.div j 8); reflexivity).
    rewrite limb8_get_nat_zero_limb8.
    reflexivity.
  - simpl bigint_digits_u63_flat.
    destruct (lt_dec j 8) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite limb8_digits_u63_length; lia).
      rewrite limb8_digits_u63_nth.
      rewrite Nat.div_small by lia.
      rewrite Nat.mod_small by lia.
      reflexivity.
    + assert (Hex : exists q, j = (8 + q)%nat).
      {
        exists (j - 8)%nat.
        lia.
      }
      destruct Hex as [q ->].
      rewrite app_nth2 by (rewrite limb8_digits_u63_length; lia).
      rewrite limb8_digits_u63_length.
      replace (8 + q - 8)%nat with q by lia.
      rewrite IH.
      replace (8 + q)%nat with (1 * 8 + q)%nat by lia.
      replace (nth ((1 * 8 + q) / 8) (x :: xs) zero_limb8)
        with (nth (q / 8) xs zero_limb8).
      2:{
        rewrite Nat.div_add_l by lia.
        simpl.
        reflexivity.
      }
      replace ((1 * 8 + q) mod 8)%nat with (q mod 8)%nat.
      2:{
        symmetry.
        rewrite Nat.add_comm.
        apply Nat.Div0.mod_add.
      }
      reflexivity.
Qed.

Lemma u63_of_nat_div8 :
  forall n,
    (Z.of_nat n < Uint63.wB)%Z ->
    Uint63.to_Z (Uint63.lsr (u63_of_nat n) limb_index_shift) =
    Z.of_nat (Nat.div n 8).
Proof.
  intros n Hn.
  unfold limb_index_shift.
  rewrite Uint63.lsr_spec.
  rewrite u63_of_nat_small by exact Hn.
  change (Uint63.to_Z (Uint63.of_Z 3)) with 3%Z.
  change (2 ^ 3)%Z with 8%Z.
  rewrite Nat2Z.inj_div by lia.
  reflexivity.
Qed.

Lemma u63_of_nat_mod8 :
  forall n,
    (Z.of_nat n < Uint63.wB)%Z ->
    Uint63.to_Z (Uint63.land (u63_of_nat n) u63_seven) =
    Z.of_nat (Nat.modulo n 8).
Proof.
  intros n Hn.
  unfold u63_seven.
  rewrite Uint63.land_spec'.
  rewrite u63_of_nat_small by exact Hn.
  change (Uint63.to_Z (Uint63.of_Z 7)) with 7%Z.
  change 7%Z with (Z.ones 3).
  rewrite Z.land_ones by lia.
  rewrite Nat2Z.inj_mod by lia.
  reflexivity.
Qed.

Lemma u63_of_nat_div8_eq :
  forall n,
    (Z.of_nat n < Uint63.wB)%Z ->
    Uint63.lsr (u63_of_nat n) limb_index_shift = u63_of_nat (Nat.div n 8).
Proof.
  intros n Hn.
  apply Uint63.to_Z_inj.
  rewrite u63_of_nat_div8 by exact Hn.
  rewrite u63_of_nat_small.
  2:{
    assert (Hdiv : (Z.of_nat (Nat.div n 8) <= Z.of_nat n)%Z).
    {
      apply Nat2Z.inj_le.
      apply Nat.Div0.div_le_upper_bound.
      lia.
    }
    lia.
  }
  reflexivity.
Qed.

Lemma u63_of_nat_mod8_eq :
  forall n,
    (Z.of_nat n < Uint63.wB)%Z ->
    Uint63.land (u63_of_nat n) u63_seven = u63_of_nat (Nat.modulo n 8).
Proof.
  intros n Hn.
  apply Uint63.to_Z_inj.
  rewrite u63_of_nat_mod8 by exact Hn.
  rewrite u63_of_nat_small.
  2:{
    assert (Hmod : (Nat.modulo n 8 < 8)%nat).
    {
      apply Nat.mod_upper_bound; lia.
    }
    change Uint63.wB with 9223372036854775808%Z.
    lia.
  }
  reflexivity.
Qed.

Lemma limb_array_of_bigint_aux_get_before :
  forall xs start acc j,
    (j < start)%nat ->
    (Z.of_nat (start + List.length xs) < Uint63.wB)%Z ->
    PArray.length acc = u63_of_nat (start + List.length xs) ->
    PArray.get (limb_array_of_bigint_aux (u63_of_nat start) xs acc) (u63_of_nat j) =
    PArray.get acc (u63_of_nat j).
Proof.
  induction xs as [|x xs IH]; intros start acc j Hj Hbound Hlen.
  - reflexivity.
  - simpl.
    simpl in Hbound.
    assert (Hsucc : (Z.of_nat (S start) < Uint63.wB)%Z).
    {
      rewrite Nat2Z.inj_succ.
      lia.
    }
    assert (Hlen' : PArray.length acc = u63_of_nat (S start + List.length xs)).
    {
      replace (u63_of_nat (S start + List.length xs)) with
        (u63_of_nat (start + List.length (x :: xs))) by (apply f_equal; simpl; lia).
      exact Hlen.
    }
    replace (u63_of_nat start + u63_one)%uint63 with (u63_of_nat (S start))
      by (symmetry; apply u63_of_nat_succ; exact Hsucc).
    assert (Hbound' : (Z.of_nat (S start + List.length xs) < Uint63.wB)%Z) by lia.
    rewrite IH.
    + rewrite PArray.get_set_other.
      * reflexivity.
      * intro Heq.
        assert (Hlhs : (Z.of_nat j < Uint63.wB)%Z) by lia.
        assert (Hrhs : (Z.of_nat start < Uint63.wB)%Z) by lia.
        pose proof (u63_of_nat_inj j start Hlhs Hrhs (eq_sym Heq)) as Hnat.
        lia.
    + lia.
    + exact Hbound'.
    + rewrite PArray.length_set. exact Hlen'.
Qed.

Lemma limb_array_of_bigint_aux_get_hit :
  forall xs start acc off,
    (off < List.length xs)%nat ->
    (Z.of_nat (start + List.length xs) < Uint63.wB)%Z ->
    PArray.length acc = u63_of_nat (start + List.length xs) ->
    PArray.default acc = zero_limb8 ->
    PArray.get (limb_array_of_bigint_aux (u63_of_nat start) xs acc) (u63_of_nat (start + off)) =
    nth off xs zero_limb8.
Proof.
  induction xs as [|x xs IH]; intros start acc off Hoff Hbound Hlen Hdef.
  - simpl in Hoff. lia.
  - destruct off as [|off'].
    + simpl.
      simpl in Hbound.
      simpl in Hoff.
      assert (Hsucc : (Z.of_nat (S start) < Uint63.wB)%Z).
      {
        rewrite Nat2Z.inj_succ.
        lia.
      }
      assert (Hlen' : PArray.length acc = u63_of_nat (S start + List.length xs)).
      {
        replace (u63_of_nat (S start + List.length xs)) with
          (u63_of_nat (start + List.length (x :: xs))) by (apply f_equal; simpl; lia).
        exact Hlen.
      }
      replace (u63_of_nat start + u63_one)%uint63 with (u63_of_nat (S start))
        by (symmetry; apply u63_of_nat_succ; exact Hsucc).
      rewrite limb_array_of_bigint_aux_get_before.
      * replace (u63_of_nat (start + 0)) with (u63_of_nat start) by (apply f_equal; lia).
        apply PArray.get_set_same.
        rewrite Hlen.
        apply u63_of_nat_ltb.
        -- simpl. lia.
        -- exact Hbound.
      * lia.
      * assert (Hbound' : (Z.of_nat (S start + List.length xs) < Uint63.wB)%Z) by lia.
        exact Hbound'.
      * rewrite PArray.length_set. exact Hlen'.
    + simpl.
      simpl in Hbound.
      assert (Hsucc : (Z.of_nat (S start) < Uint63.wB)%Z).
      {
        rewrite Nat2Z.inj_succ.
        lia.
      }
      assert (Hlen' : PArray.length acc = u63_of_nat (S start + List.length xs)).
      {
        replace (u63_of_nat (S start + List.length xs)) with
          (u63_of_nat (start + List.length (x :: xs))) by (apply f_equal; simpl; lia).
        exact Hlen.
      }
      replace (u63_of_nat start + u63_one)%uint63 with (u63_of_nat (S start))
        by (symmetry; apply u63_of_nat_succ; exact Hsucc).
      replace (u63_of_nat (start + S off')) with (u63_of_nat (S start + off'))
        by (apply f_equal; lia).
      apply IH.
      * apply Nat.succ_lt_mono in Hoff. exact Hoff.
      * assert (Hbound' : (Z.of_nat (S start + List.length xs) < Uint63.wB)%Z) by lia.
        exact Hbound'.
      * rewrite PArray.length_set. exact Hlen'.
      * rewrite PArray.default_set. exact Hdef.
Qed.

Lemma limb_array_of_bigint_get_limb :
  forall xs j,
    (j < List.length xs)%nat ->
    (Z.of_nat (List.length xs) <= Uint63.to_Z PArray.max_length)%Z ->
    PArray.get (limb_array_of_bigint xs) (u63_of_nat j) = nth j xs zero_limb8.
Proof.
  intros xs j Hj Hxs.
  unfold limb_array_of_bigint.
  replace (u63_of_nat j) with (u63_of_nat (0%nat + j)) by reflexivity.
  pose proof (limb_array_of_bigint_aux_get_hit xs 0%nat
                (PArray.make (u63_of_nat (List.length xs)) zero_limb8) j) as Hhit.
  specialize (Hhit Hj).
  assert (Hbound0 : (Z.of_nat (0%nat + List.length xs) < Uint63.wB)%Z).
  {
    eapply Z.le_lt_trans.
    - apply Hxs.
    - apply Uint63.to_Z_bounded.
  }
  specialize (Hhit Hbound0).
  assert (Hlen0 :
    PArray.length (PArray.make (u63_of_nat (List.length xs)) zero_limb8) =
    u63_of_nat (0%nat + List.length xs)).
  {
    rewrite PArray.length_make.
    assert (Hleb : (u63_of_nat (List.length xs) ≤? PArray.max_length)%uint63 = true).
    {
      apply Uint63.leb_spec.
      rewrite u63_of_nat_small.
      - exact Hxs.
      - eapply Z.le_lt_trans; [apply Hxs|apply Uint63.to_Z_bounded].
    }
    rewrite Hleb.
    reflexivity.
  }
  specialize (Hhit Hlen0).
  assert (Hdef0 :
    PArray.default (PArray.make (u63_of_nat (List.length xs)) zero_limb8) = zero_limb8).
  {
    rewrite PArray.default_make.
    reflexivity.
  }
  specialize (Hhit Hdef0).
  exact Hhit.
Qed.

Lemma limb_array_of_bigint_get_default :
  forall xs j,
    (List.length xs <= j)%nat ->
    (Z.of_nat j < Uint63.wB)%Z ->
    (Z.of_nat (List.length xs) <= Uint63.to_Z PArray.max_length)%Z ->
    PArray.get (limb_array_of_bigint xs) (u63_of_nat j) = zero_limb8.
Proof.
  intros xs j Hj HjB Hxs.
  transitivity (PArray.default (limb_array_of_bigint xs)).
  - apply PArray.get_out_of_bounds.
    rewrite limb_array_of_bigint_length by exact Hxs.
    apply Bool.not_true_is_false.
    intro Hlt.
    apply Uint63.ltb_spec in Hlt.
    assert (HlenB : (Z.of_nat (List.length xs) < Uint63.wB)%Z).
    {
      eapply Z.le_lt_trans; [apply Hxs|apply Uint63.to_Z_bounded].
    }
    rewrite (u63_of_nat_small j HjB) in Hlt.
    rewrite (u63_of_nat_small (List.length xs) HlenB) in Hlt.
    lia.
  - unfold limb_array_of_bigint.
    rewrite limb_array_of_bigint_aux_default.
    rewrite PArray.default_make.
    reflexivity.
Qed.

Lemma limb_array_get_digit_of_bigint :
  forall xs j,
    (Z.of_nat j < Uint63.wB)%Z ->
    (Z.of_nat (List.length xs) <= Uint63.to_Z PArray.max_length)%Z ->
    limb_array_get_digit (limb_array_of_bigint xs) (u63_of_nat j) =
    nth j (bigint_digits_u63_flat xs) zero_digit.
Proof.
  intros xs j Hj Hxs.
  unfold limb_array_get_digit.
  rewrite u63_of_nat_div8_eq by exact Hj.
  rewrite u63_of_nat_mod8_eq by exact Hj.
  rewrite limb8_get_nat_eq.
  2:{ apply Nat.mod_upper_bound; lia. }
  rewrite nth_bigint_digits_u63_flat.
  destruct (lt_dec (Nat.div j 8) (List.length xs)) as [Hlt|Hge].
  - rewrite limb_array_of_bigint_get_limb by assumption.
    reflexivity.
  - rewrite limb_array_of_bigint_get_default.
    + replace (nth (Nat.div j 8) xs zero_limb8) with zero_limb8.
      2:{
        symmetry.
        apply nth_overflow.
        apply Nat.nlt_ge.
        exact Hge.
      }
      rewrite limb8_get_nat_zero_limb8.
      reflexivity.
    + apply Nat.nlt_ge.
      exact Hge.
    + assert (HdivZ : (Z.of_nat (Nat.div j 8) = Z.of_nat j / 8)%Z).
      {
        rewrite Nat2Z.inj_div by lia.
        reflexivity.
      }
      rewrite HdivZ.
      eapply Z.le_lt_trans with (m := Z.of_nat j).
      * apply Z.div_le_upper_bound.
        -- lia.
        -- nia.
      * exact Hj.
    + exact Hxs.
Qed.

Lemma u63_of_nat_add :
  forall m n,
    (Z.of_nat (m + n) < Uint63.wB)%Z ->
    (u63_of_nat m + u63_of_nat n)%uint63 = u63_of_nat (m + n).
Proof.
  intros m n Hmn.
  apply Uint63.to_Z_inj.
  rewrite Uint63.add_spec.
  rewrite !u63_of_nat_small by lia.
  rewrite Z.mod_small by lia.
  rewrite Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma u63_mul2_nat :
  forall n,
    (Z.of_nat (2 * n) < Uint63.wB)%Z ->
    u63_mul2 (u63_of_nat n) = u63_of_nat (2 * n).
Proof.
  intros n Hn.
  unfold u63_mul2.
  replace (2 * n)%nat with (n + n)%nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma u63_mul3_nat :
  forall n,
    (Z.of_nat (3 * n) < Uint63.wB)%Z ->
    u63_mul3 (u63_of_nat n) = u63_of_nat (3 * n).
Proof.
  intros n Hn.
  unfold u63_mul3.
  rewrite u63_mul2_nat by lia.
  replace (3 * n)%nat with (2 * n + n)%nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma u63_mul4_nat :
  forall n,
    (Z.of_nat (4 * n) < Uint63.wB)%Z ->
    u63_mul4 (u63_of_nat n) = u63_of_nat (4 * n).
Proof.
  intros n Hn.
  unfold u63_mul4.
  replace (4 * n)%nat with (2 * (2 * n))%nat by lia.
  rewrite u63_mul2_nat by lia.
  rewrite u63_mul2_nat by lia.
  reflexivity.
Qed.

Lemma u63_mul5_nat :
  forall n,
    (Z.of_nat (5 * n) < Uint63.wB)%Z ->
    u63_mul5 (u63_of_nat n) = u63_of_nat (5 * n).
Proof.
  intros n Hn.
  unfold u63_mul5.
  rewrite u63_mul4_nat by lia.
  replace (5 * n)%nat with (4 * n + n)%nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma u63_mul6_nat :
  forall n,
    (Z.of_nat (6 * n) < Uint63.wB)%Z ->
    u63_mul6 (u63_of_nat n) = u63_of_nat (6 * n).
Proof.
  intros n Hn.
  unfold u63_mul6.
  rewrite u63_mul4_nat by lia.
  rewrite u63_mul2_nat by lia.
  replace (6 * n)%nat with (4 * n + 2 * n)%nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma u63_mul7_nat :
  forall n,
    (Z.of_nat (7 * n) < Uint63.wB)%Z ->
    u63_mul7 (u63_of_nat n) = u63_of_nat (7 * n).
Proof.
  intros n Hn.
  unfold u63_mul7.
  rewrite u63_mul4_nat by lia.
  rewrite u63_mul3_nat by lia.
  replace (7 * n)%nat with (4 * n + 3 * n)%nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_0_nat :
  forall base step,
    block_index_0 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 0 * step).
Proof.
  intros base step.
  unfold block_index_0.
  replace (base + 0 * step)%nat with base by lia.
  reflexivity.
Qed.

Lemma block_index_1_nat :
  forall base step,
    (Z.of_nat (base + 4 * step) < Uint63.wB)%Z ->
    block_index_1 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 4 * step).
Proof.
  intros base step H.
  unfold block_index_1.
  rewrite u63_mul4_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_2_nat :
  forall base step,
    (Z.of_nat (base + 2 * step) < Uint63.wB)%Z ->
    block_index_2 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 2 * step).
Proof.
  intros base step H.
  unfold block_index_2.
  rewrite u63_mul2_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_3_nat :
  forall base step,
    (Z.of_nat (base + 6 * step) < Uint63.wB)%Z ->
    block_index_3 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 6 * step).
Proof.
  intros base step H.
  unfold block_index_3.
  rewrite u63_mul6_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_4_nat :
  forall base step,
    (Z.of_nat (base + step) < Uint63.wB)%Z ->
    block_index_4 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + step).
Proof.
  intros base step H.
  unfold block_index_4.
  apply u63_of_nat_add; exact H.
Qed.

Lemma block_index_5_nat :
  forall base step,
    (Z.of_nat (base + 5 * step) < Uint63.wB)%Z ->
    block_index_5 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 5 * step).
Proof.
  intros base step H.
  unfold block_index_5.
  rewrite u63_mul5_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_6_nat :
  forall base step,
    (Z.of_nat (base + 3 * step) < Uint63.wB)%Z ->
    block_index_6 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 3 * step).
Proof.
  intros base step H.
  unfold block_index_6.
  rewrite u63_mul3_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma block_index_7_nat :
  forall base step,
    (Z.of_nat (base + 7 * step) < Uint63.wB)%Z ->
    block_index_7 (u63_of_nat base) (u63_of_nat step) = u63_of_nat (base + 7 * step).
Proof.
  intros base step H.
  unfold block_index_7.
  rewrite u63_mul7_nat by lia.
  apply u63_of_nat_add; lia.
Qed.

Lemma prime469_pow2_ge_two :
  forall k, (2 <= Prime469.pow2 (S (S (S k))))%nat.
Proof.
  intro k.
  pose proof (Prime469.pow2_pos k) as Hk.
  repeat rewrite Prime469.pow2_succ.
  lia.
Qed.

Lemma prime469_parent_bound_ge_step2 :
  forall k base step,
    (step + step <=
     base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime469.pow2 (S (S (S k)))).
  assert (Hm : (2 <= m + m - 1)%nat).
  {
    subst m.
    pose proof (prime469_pow2_ge_two k) as Hpow.
    lia.
  }
  replace (step + step)%nat with (step * 2)%nat by lia.
  assert (Hmul : (step * 2 <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma prime469_even_subtree_bound_le_parent :
  forall k base step,
    (base + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1) <=
     base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime469.pow2 (S (S (S k)))).
  assert (Hm : (2 * (m - 1) <= m + m - 1)%nat).
  {
    subst m.
    pose proof (Prime469.pow2_pos (S (S (S k)))) as Hpow.
    lia.
  }
  replace ((2 * step) * (m - 1))%nat with (step * (2 * (m - 1)))%nat by lia.
  assert (Hmul : (step * (2 * (m - 1)) <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma prime469_parent_bound_ge_base_step :
  forall k base step,
    (base + step <=
     base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime469.pow2 (S (S (S k)))).
  assert (Hm : (1 <= m + m - 1)%nat).
  {
    subst m.
    pose proof (Prime469.pow2_pos (S (S (S k)))) as Hpow.
    lia.
  }
  assert (Hmul : (step * 1 <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma odd_subtree_parent_index :
  forall base step m,
    (0 < m)%nat ->
    ((base + step) + (2 * step) * (m - 1) = base + step * (m + m - 1))%nat.
Proof.
  intros base step [|m] Hm.
  - lia.
  - replace (S m - 1)%nat with m by lia.
    replace (S m + S m - 1)%nat with (S (m + m))%nat by lia.
    nia.
Qed.

Lemma prime469_input_get_packed_tree_from_limb_array :
  forall k arr base step i,
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (base + step * (Prime469.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z ->
    Prime469.input_get (S (S (S k)))
      (Prime469.unpack_tree8 k
        (packed_tree_from_limb_array Prime469.Block8 k arr (u63_of_nat base) (u63_of_nat step))) i =
    limb_array_get_digit arr (u63_of_nat (base + step * i)).
Proof.
  induction k as [|k IH]; intros arr base step i Hi Hbound.
  - destruct i as [|i].
    + simpl.
      replace (base + step * 0)%nat with (base + 0 * step)%nat by lia.
      rewrite block_index_0_nat.
      reflexivity.
    + destruct i as [|i].
      * simpl.
        replace (base + step * 1)%nat with (base + step)%nat by lia.
        rewrite block_index_4_nat.
        2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
        reflexivity.
      * destruct i as [|i].
        -- simpl.
           replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
           rewrite block_index_2_nat.
           2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
           reflexivity.
        -- destruct i as [|i].
           ++ simpl.
              replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
              rewrite block_index_6_nat.
              2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
              reflexivity.
           ++ destruct i as [|i].
              ** simpl.
                 replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
                 rewrite block_index_1_nat.
                 2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                 reflexivity.
              ** destruct i as [|i].
                 --- simpl.
                     replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
                     rewrite block_index_5_nat.
                     2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                     reflexivity.
                 --- destruct i as [|i].
                     { simpl.
                       replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
                       rewrite block_index_3_nat.
                       2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                       reflexivity. }
                     { destruct i as [|i].
                       - simpl.
                         replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
                         rewrite block_index_7_nat.
                         2:{ change (Prime469.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                         reflexivity.
                       - change (Prime469.pow2 3) with 8%nat in Hi.
                         simpl in Hi.
                         lia. }
  - simpl Prime469.unpack_tree8.
    simpl packed_tree_from_limb_array.
    simpl Prime469.input_get.
    destruct (Nat.even i) eqn:Heven.
    + apply Nat.even_spec in Heven.
      destruct Heven as [q Hq].
      subst i.
      rewrite Nat.div2_even.
      assert (Hstep2 : (Z.of_nat (step + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime469.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime469_parent_bound_ge_step2 k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step)) with (u63_of_nat (2 * step)).
      2:{
        replace (2 * step)%nat with (step + step)%nat by lia.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2.
      }
      replace (base + step * (2 * q))%nat with (base + (2 * step) * q)%nat by lia.
      apply IH.
      * rewrite Prime469.pow2_succ in Hi.
        lia.
      * pose proof Hbound as Hb.
        rewrite Prime469.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime469_even_subtree_bound_le_parent k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
    + assert (Hodd : Nat.Odd i).
      {
        apply Nat.odd_spec.
        rewrite <- Nat.negb_even.
        now rewrite Heven.
      }
      destruct Hodd as [q Hq].
      subst i.
      rewrite Nat.div2_odd'.
      assert (Hstep2 : (Z.of_nat (step + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime469.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime469_parent_bound_ge_step2 k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step)) with (u63_of_nat (2 * step)).
      2:{
        replace (2 * step)%nat with (step + step)%nat by lia.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2.
      }
      assert (Hbase_step : (Z.of_nat (base + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime469.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime469_parent_bound_ge_base_step k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat base) (u63_of_nat step)) with (u63_of_nat (base + step)).
      2:{
        symmetry.
        apply u63_of_nat_add.
        exact Hbase_step.
      }
      replace (base + step * (2 * q + 1))%nat with ((base + step) + (2 * step) * q)%nat by lia.
      apply IH.
      * rewrite Prime469.pow2_succ in Hi.
        lia.
      * pose proof Hbound as Hb.
        rewrite Prime469.pow2_succ in Hb.
        replace ((base + step) + (2 * step) * (Prime469.pow2 (S (S (S k))) - 1))%nat
          with (base + step * (Prime469.pow2 (S (S (S k))) + Prime469.pow2 (S (S (S k))) - 1))%nat by
            (symmetry;
             apply odd_subtree_parent_index;
             apply Prime469.pow2_pos).
        exact Hb.
Qed.

Lemma prime469_transform_bound :
  forall k,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (Prime469.pow2 (S (S (S k))) - 1) < Uint63.wB)%Z.
Proof.
  intros k Hk.
  unfold supported_max_block_log in Hk.
  cbn in Hk.
  assert (Hle : (Prime469.pow2 (S (S (S k))) - 1 <= Prime469.pow2 23 - 1)%nat).
  {
    unfold Prime469.pow2.
    change (23%nat) with (3 + 20)%nat.
    assert (Hexp : (S (S (S k)) <= 3 + 20)%nat) by lia.
    apply Nat.sub_le_mono_r.
    apply Nat.pow_le_mono_r.
    - lia.
    - exact Hexp.
  }
  apply Nat2Z.inj_le in Hle.
  eapply Z.le_lt_trans; [exact Hle|].
  vm_compute.
  reflexivity.
Qed.

Lemma prime469_transform_size_bound :
  forall k,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (Prime469.pow2 (S (S (S k)))) < Uint63.wB)%Z.
Proof.
  intros k Hk.
  unfold supported_max_block_log in Hk.
  cbn in Hk.
  assert (Hle : (Prime469.pow2 (S (S (S k))) <= Prime469.pow2 23)%nat).
  {
    unfold Prime469.pow2.
    assert (Hexp : (S (S (S k)) <= 3 + 20)%nat) by lia.
    apply Nat.pow_le_mono_r.
    - lia.
    - exact Hexp.
  }
  apply Nat2Z.inj_le in Hle.
  eapply Z.le_lt_trans; [exact Hle|].
  vm_compute.
  reflexivity.
Qed.

Lemma build_tree469_input_get :
  forall k x i,
    (k <= supported_max_block_log)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime469.input_get (S (S (S k)))
      (Prime469.unpack_tree8 k (build_tree469 k x)) i =
    nth i (bigint_digits_u63_flat x) zero_digit.
Proof.
  intros k x i Hk Hi Hlen.
  unfold build_tree469.
  change zero_digit with (u63_of_nat 0).
  change u63_one with (u63_of_nat 1).
  rewrite prime469_input_get_packed_tree_from_limb_array.
  2: exact Hi.
  2:{
    replace (0 + 1 * (Prime469.pow2 (S (S (S k))) - 1))%nat
      with (Prime469.pow2 (S (S (S k))) - 1)%nat by lia.
    apply prime469_transform_bound.
    exact Hk.
  }
  replace (0 + 1 * i)%nat with i by lia.
  rewrite limb_array_get_digit_of_bigint.
  - reflexivity.
  - eapply Z.lt_trans with (m := Z.of_nat (Prime469.pow2 (S (S (S k))))).
    + apply Nat2Z.inj_lt.
      exact Hi.
    + apply prime469_transform_size_bound.
      exact Hk.
  - exact Hlen.
Qed.

Lemma prime181_pow2_ge_two :
  forall k, (2 <= Prime181.pow2 (S (S (S k))))%nat.
Proof.
  intro k.
  pose proof (Prime181.pow2_pos k) as Hk.
  repeat rewrite Prime181.pow2_succ.
  lia.
Qed.

Lemma prime181_parent_bound_ge_step2 :
  forall k base step,
    (step + step <=
     base + step * (Prime181.pow2 (S (S (S k))) + Prime181.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime181.pow2 (S (S (S k)))).
  assert (Hm : (2 <= m + m - 1)%nat).
  {
    subst m.
    pose proof (prime181_pow2_ge_two k) as Hpow.
    lia.
  }
  replace (step + step)%nat with (step * 2)%nat by lia.
  assert (Hmul : (step * 2 <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma prime181_even_subtree_bound_le_parent :
  forall k base step,
    (base + (2 * step) * (Prime181.pow2 (S (S (S k))) - 1) <=
     base + step * (Prime181.pow2 (S (S (S k))) + Prime181.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime181.pow2 (S (S (S k)))).
  assert (Hm : (2 * (m - 1) <= m + m - 1)%nat).
  {
    subst m.
    pose proof (Prime181.pow2_pos (S (S (S k)))) as Hpow.
    lia.
  }
  replace ((2 * step) * (m - 1))%nat with (step * (2 * (m - 1)))%nat by lia.
  assert (Hmul : (step * (2 * (m - 1)) <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma prime181_parent_bound_ge_base_step :
  forall k base step,
    (base + step <=
     base + step * (Prime181.pow2 (S (S (S k))) + Prime181.pow2 (S (S (S k))) - 1))%nat.
Proof.
  intros k base step.
  set (m := Prime181.pow2 (S (S (S k)))).
  assert (Hm : (1 <= m + m - 1)%nat).
  {
    subst m.
    pose proof (Prime181.pow2_pos (S (S (S k)))) as Hpow.
    lia.
  }
  assert (Hmul : (step * 1 <= step * (m + m - 1))%nat).
  {
    apply Nat.mul_le_mono_nonneg_l; lia.
  }
  lia.
Qed.

Lemma prime181_input_get_packed_tree_from_limb_array :
  forall k arr base step i,
    (i < Prime181.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (base + step * (Prime181.pow2 (S (S (S k))) - 1)) < Uint63.wB)%Z ->
    Prime181.input_get (S (S (S k)))
      (Prime181.unpack_tree8 k
        (packed_tree_from_limb_array Prime181.Block8 k arr (u63_of_nat base) (u63_of_nat step))) i =
    limb_array_get_digit arr (u63_of_nat (base + step * i)).
Proof.
  induction k as [|k IH]; intros arr base step i Hi Hbound.
  - destruct i as [|i].
    + simpl.
      replace (base + step * 0)%nat with (base + 0 * step)%nat by lia.
      rewrite block_index_0_nat.
      reflexivity.
    + destruct i as [|i].
      * simpl.
        replace (base + step * 1)%nat with (base + step)%nat by lia.
        rewrite block_index_4_nat.
        2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
        reflexivity.
      * destruct i as [|i].
        -- simpl.
           replace (base + step * 2)%nat with (base + 2 * step)%nat by lia.
           rewrite block_index_2_nat.
           2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
           reflexivity.
        -- destruct i as [|i].
           ++ simpl.
              replace (base + step * 3)%nat with (base + 3 * step)%nat by lia.
              rewrite block_index_6_nat.
              2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
              reflexivity.
           ++ destruct i as [|i].
              ** simpl.
                 replace (base + step * 4)%nat with (base + 4 * step)%nat by lia.
                 rewrite block_index_1_nat.
                 2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                 reflexivity.
              ** destruct i as [|i].
                 --- simpl.
                     replace (base + step * 5)%nat with (base + 5 * step)%nat by lia.
                     rewrite block_index_5_nat.
                     2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                     reflexivity.
                 --- destruct i as [|i].
                     { simpl.
                       replace (base + step * 6)%nat with (base + 6 * step)%nat by lia.
                       rewrite block_index_3_nat.
                       2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                       reflexivity. }
                     { destruct i as [|i].
                       - simpl.
                         replace (base + step * 7)%nat with (base + 7 * step)%nat by lia.
                         rewrite block_index_7_nat.
                         2:{ change (Prime181.pow2 3) with 8%nat in Hbound; simpl in Hbound; lia. }
                         reflexivity.
                       - change (Prime181.pow2 3) with 8%nat in Hi.
                         simpl in Hi.
                         lia. }
  - simpl Prime181.unpack_tree8.
    simpl packed_tree_from_limb_array.
    simpl Prime181.input_get.
    destruct (Nat.even i) eqn:Heven.
    + apply Nat.even_spec in Heven.
      destruct Heven as [q Hq].
      subst i.
      rewrite Nat.div2_even.
      assert (Hstep2 : (Z.of_nat (step + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime181.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime181_parent_bound_ge_step2 k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step)) with (u63_of_nat (2 * step)).
      2:{
        replace (2 * step)%nat with (step + step)%nat by lia.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2.
      }
      replace (base + step * (2 * q))%nat with (base + (2 * step) * q)%nat by lia.
      apply IH.
      * rewrite Prime181.pow2_succ in Hi.
        lia.
      * pose proof Hbound as Hb.
        rewrite Prime181.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime181_even_subtree_bound_le_parent k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
    + assert (Hodd : Nat.Odd i).
      {
        apply Nat.odd_spec.
        rewrite <- Nat.negb_even.
        now rewrite Heven.
      }
      destruct Hodd as [q Hq].
      subst i.
      rewrite Nat.div2_odd'.
      assert (Hstep2 : (Z.of_nat (step + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime181.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime181_parent_bound_ge_step2 k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat step) (u63_of_nat step)) with (u63_of_nat (2 * step)).
      2:{
        replace (2 * step)%nat with (step + step)%nat by lia.
        symmetry.
        apply u63_of_nat_add.
        exact Hstep2.
      }
      assert (Hbase_step : (Z.of_nat (base + step) < Uint63.wB)%Z).
      {
        pose proof Hbound as Hb.
        rewrite Prime181.pow2_succ in Hb.
        eapply Z.le_lt_trans.
        2: exact Hb.
        pose proof (prime181_parent_bound_ge_base_step k base step) as Hnat.
        apply Nat2Z.inj_le in Hnat.
        exact Hnat.
      }
      replace (Uint63.add (u63_of_nat base) (u63_of_nat step)) with (u63_of_nat (base + step)).
      2:{
        symmetry.
        apply u63_of_nat_add.
        exact Hbase_step.
      }
      replace (base + step * (2 * q + 1))%nat with ((base + step) + (2 * step) * q)%nat by lia.
      apply IH.
      * rewrite Prime181.pow2_succ in Hi.
        lia.
      * pose proof Hbound as Hb.
        rewrite Prime181.pow2_succ in Hb.
        replace ((base + step) + (2 * step) * (Prime181.pow2 (S (S (S k))) - 1))%nat
          with (base + step * (Prime181.pow2 (S (S (S k))) + Prime181.pow2 (S (S (S k))) - 1))%nat by
            (symmetry;
             apply odd_subtree_parent_index;
             apply Prime181.pow2_pos).
        exact Hb.
Qed.

Lemma prime181_transform_bound :
  forall k,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (Prime181.pow2 (S (S (S k))) - 1) < Uint63.wB)%Z.
Proof.
  intros k Hk.
  unfold supported_max_block_log in Hk.
  cbn in Hk.
  assert (Hle : (Prime181.pow2 (S (S (S k))) - 1 <= Prime181.pow2 23 - 1)%nat).
  {
    unfold Prime181.pow2.
    change (23%nat) with (3 + 20)%nat.
    assert (Hexp : (S (S (S k)) <= 3 + 20)%nat) by lia.
    apply Nat.sub_le_mono_r.
    apply Nat.pow_le_mono_r.
    - lia.
    - exact Hexp.
  }
  apply Nat2Z.inj_le in Hle.
  eapply Z.le_lt_trans; [exact Hle|].
  vm_compute.
  reflexivity.
Qed.

Lemma prime181_transform_size_bound :
  forall k,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (Prime181.pow2 (S (S (S k)))) < Uint63.wB)%Z.
Proof.
  intros k Hk.
  unfold supported_max_block_log in Hk.
  cbn in Hk.
  assert (Hle : (Prime181.pow2 (S (S (S k))) <= Prime181.pow2 23)%nat).
  {
    unfold Prime181.pow2.
    assert (Hexp : (S (S (S k)) <= 3 + 20)%nat) by lia.
    apply Nat.pow_le_mono_r.
    - lia.
    - exact Hexp.
  }
  apply Nat2Z.inj_le in Hle.
  eapply Z.le_lt_trans; [exact Hle|].
  vm_compute.
  reflexivity.
Qed.

Lemma build_tree181_input_get :
  forall k x i,
    (k <= supported_max_block_log)%nat ->
    (i < Prime181.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime181.input_get (S (S (S k)))
      (Prime181.unpack_tree8 k (build_tree181 k x)) i =
    nth i (bigint_digits_u63_flat x) zero_digit.
Proof.
  intros k x i Hk Hi Hlen.
  unfold build_tree181.
  change zero_digit with (u63_of_nat 0).
  change u63_one with (u63_of_nat 1).
  rewrite prime181_input_get_packed_tree_from_limb_array.
  2: exact Hi.
  2:{
    replace (0 + 1 * (Prime181.pow2 (S (S (S k))) - 1))%nat
      with (Prime181.pow2 (S (S (S k))) - 1)%nat by lia.
    apply prime181_transform_bound.
    exact Hk.
  }
  replace (0 + 1 * i)%nat with i by lia.
  rewrite limb_array_get_digit_of_bigint.
  - reflexivity.
  - eapply Z.lt_trans with (m := Z.of_nat (Prime181.pow2 (S (S (S k))))).
    + apply Nat2Z.inj_lt.
      exact Hi.
    + apply prime181_transform_size_bound.
      exact Hk.
  - exact Hlen.
Qed.
