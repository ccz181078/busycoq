From Coq Require Import Uint63 ZArith Lia Lists.List Array.PArray.
Require Import BigInt.NTTConvolution BigInt.NTTSpectral BigInt.NTTConcrete
  BigInt.BigIntMul BigInt.BigIntMulProof BigInt.BigIntMulCanonical
  BigInt.BigIntMulCoefficients BigInt.BigIntMulNormalize BigInt.BigIntMulCRTArithmetic.

Import ListNotations.
Local Open Scope Z_scope.

Module Prime469Conv := TreeNTTConvolution(Prime469Cfg).
Module Prime181Conv := TreeNTTConvolution(Prime181Cfg).

Lemma zsum_nat_ext :
  forall n (f g : nat -> Z),
    (forall i, (i < n)%nat -> f i = g i) ->
    zsum_nat n f = zsum_nat n g.
Proof.
  induction n as [|n IH]; intros f g Hfg.
  - reflexivity.
  - simpl.
    rewrite (IH f g).
    2:{
      intros i Hi.
      apply Hfg.
      lia.
    }
    rewrite Hfg by lia.
    reflexivity.
Qed.

Lemma zsum_nat_zero :
  forall n,
    zsum_nat n (fun _ => 0) = 0.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    lia.
Qed.

Lemma zsum_nat_eqb_none :
  forall len idx (f : nat -> Z),
    (len <= idx)%nat ->
    zsum_nat len (fun j => if Nat.eqb j idx then f j else 0) = 0.
Proof.
  induction len as [|len IH]; intros idx f Hidx.
  - reflexivity.
  - simpl.
    rewrite (IH idx f) by lia.
    destruct (Nat.eqb_spec len idx); lia.
Qed.

Lemma zsum_nat_eqb_single :
  forall len idx (f : nat -> Z),
    (idx < len)%nat ->
    zsum_nat len (fun j => if Nat.eqb j idx then f j else 0) = f idx.
Proof.
  induction len as [|len IH]; intros idx f Hidx.
  - lia.
  - simpl.
    destruct (Nat.eq_dec idx len) as [->|Hneq].
    + rewrite Nat.eqb_refl.
      rewrite zsum_nat_eqb_none by lia.
      lia.
    + destruct (Nat.eqb idx len) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        lia.
      * assert (Heq' : (len =? idx)%nat = false).
        {
          apply Nat.eqb_neq.
          lia.
        }
        rewrite Heq'.
        rewrite (IH idx f) by lia.
        lia.
Qed.

Lemma zsum_nat_cutoff_zero :
  forall len cutoff (f : nat -> Z),
    (cutoff <= len)%nat ->
    (forall j, (cutoff <= j < len)%nat -> f j = 0) ->
    zsum_nat len f = zsum_nat cutoff f.
Proof.
  induction len as [|len IH]; intros cutoff f Hcutoff Hzero.
  - assert (cutoff = 0)%nat by lia.
    subst cutoff.
    reflexivity.
  - destruct (Nat.eq_dec cutoff (S len)) as [->|Hneq].
    + reflexivity.
    + simpl.
      rewrite (IH cutoff f).
      2: lia.
      2:{
        intros j Hj.
        apply Hzero.
        lia.
      }
      rewrite Hzero by lia.
      lia.
Qed.

Lemma nth_map_default :
  forall (A B : Type) (f : A -> B) xs d i,
    nth i (map f xs) (f d) = f (nth i xs d).
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros d i.
  - destruct i; reflexivity.
  - destruct i; simpl; [reflexivity|apply IH].
Qed.

Lemma nth_bigint_digits_z :
  forall x i,
    nth i (bigint_digits_z x) 0 =
    Uint63.to_Z (nth i (bigint_digits_u63_flat x) zero_digit).
Proof.
  intros x i.
  rewrite bigint_digits_z_eq_flat.
  unfold bigint_digits_z_flat.
  change 0 with (Uint63.to_Z zero_digit).
  rewrite nth_map_default with (d := zero_digit).
  reflexivity.
Qed.

Lemma nth_cons_sub_shift :
  forall (A : Type) i l (x : A) xs d,
    (l <= i)%nat ->
    nth (S i - l) (x :: xs) d = nth (i - l) xs d.
Proof.
  intros A i l x xs d Hle.
  replace (S i - l)%nat with (S (i - l)) by lia.
  reflexivity.
Qed.

Lemma zsum_nat_succ_shift :
  forall n (f : nat -> Z),
    zsum_nat (S n) f = f 0%nat + zsum_nat n (fun j => f (S j)).
Proof.
  induction n as [|n IH]; intros f.
  - simpl.
    lia.
  - change (zsum_nat (S n) f + f (S n) =
            f 0%nat + (zsum_nat n (fun j => f (S j)) + f (S n))).
    rewrite IH.
    lia.
Qed.

Lemma convolution_coeff_zsum_nat :
  forall xs ys i,
    convolution_coeff xs ys i =
    zsum_nat (S i) (fun j => nth j xs 0 * nth (i - j) ys 0).
Proof.
  induction xs as [|x xs IH]; intros ys i.
  - rewrite zsum_nat_ext with (g := fun _ => 0).
    2:{
      intros j Hj.
      destruct j; reflexivity.
    }
    rewrite zsum_nat_zero.
    reflexivity.
  - destruct i as [|i].
    + cbn [convolution_coeff].
      rewrite zsum_nat_succ_shift.
      simpl.
      lia.
    + cbn [convolution_coeff].
      rewrite zsum_nat_succ_shift.
      rewrite zsum_nat_ext with
        (g := fun j => nth j xs 0 * nth (i - j) ys 0).
      2:{
        intros j Hj.
        simpl.
        replace (S i - S j)%nat with (i - j)%nat by lia.
        reflexivity.
      }
      rewrite IH.
      reflexivity.
Qed.

Lemma convolution_coeff_zsum_nat_len :
  forall xs ys len i,
    (S i <= len)%nat ->
    convolution_coeff xs ys i =
    zsum_nat len (fun j => if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
Proof.
  intros xs ys len i Hlen.
  rewrite convolution_coeff_zsum_nat.
  rewrite zsum_nat_cutoff_zero with
    (cutoff := S i)
    (f := fun j => if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
  2: lia.
  2:{
    intros j Hj.
    destruct (Nat.leb_spec0 j i); lia.
  }
  apply zsum_nat_ext.
  intros j Hj.
  destruct (Nat.leb_spec0 j i); [reflexivity|lia].
Qed.

Lemma convolution_wrap_term_zero :
  forall xs ys len i j,
    (List.length xs + List.length ys <= len)%nat ->
    (j < len)%nat ->
    (i < j)%nat ->
    nth j xs 0 * nth (len + i - j) ys 0 = 0.
Proof.
  intros xs ys len i j Hsum Hj Hij.
  destruct (lt_dec j (List.length xs)) as [Hxs|Hxs].
  - assert (Hys0 : (List.length ys <= len - j)%nat) by lia.
    assert (Hys : (List.length ys <= len + i - j)%nat).
    {
      eapply Nat.le_trans; [exact Hys0|].
      lia.
    }
    rewrite nth_overflow with (n := (len + i - j)%nat) (l := ys) (d := 0) by exact Hys.
    lia.
  - rewrite nth_overflow with (n := j) (l := xs) (d := 0) by lia.
    lia.
Qed.

Lemma prime469_zsum_mod :
  forall n (f : nat -> Z),
    Prime469.zsum n (fun j => Prime469.zcanon (f j)) =
    Prime469.zcanon (zsum_nat n f).
Proof.
  induction n as [|n IH]; intro f.
  - reflexivity.
  - simpl.
    rewrite (IH f).
    unfold Prime469.zadd.
    rewrite Prime469.zcanon_add.
    reflexivity.
Qed.

Lemma prime181_zsum_mod :
  forall n (f : nat -> Z),
    Prime181.zsum n (fun j => Prime181.zcanon (f j)) =
    Prime181.zcanon (zsum_nat n f).
Proof.
  induction n as [|n IH]; intro f.
  - reflexivity.
  - simpl.
    rewrite (IH f).
    unfold Prime181.zadd.
    rewrite Prime181.zcanon_add.
    reflexivity.
Qed.

Lemma prime469_value_build_tree_input :
  forall k x i,
    (k <= supported_max_block_log)%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime469.value
      (Prime469.input_get (S (S (S k)))
        (Prime469.unpack_tree8 k (build_tree469 k x)) i) =
    nth i (bigint_digits_z x) 0.
Proof.
  intros k x i Hk Hi Hlen.
  rewrite build_tree469_input_get by assumption.
  rewrite <- nth_bigint_digits_z.
  reflexivity.
Qed.

Lemma prime469_selected_term :
  forall len i j xs ys,
    (List.length xs + List.length ys <= len)%nat ->
    (j < len)%nat ->
    Prime469.zmul (Prime469.zcanon (nth j xs 0))
      (if Nat.leb j i
       then Prime469.zcanon (nth (i - j) ys 0)
       else Prime469.zcanon (nth (len + i - j) ys 0)) =
    Prime469.zcanon
      (if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
Proof.
  intros len i j xs ys Hsum Hj.
  destruct (Nat.leb j i) eqn:Hji.
  - apply Nat.leb_le in Hji.
    unfold Prime469.zmul.
    rewrite Prime469.zcanon_mul.
    reflexivity.
  - apply Nat.leb_gt in Hji.
    unfold Prime469.zmul.
    rewrite Prime469.zcanon_mul.
    rewrite (convolution_wrap_term_zero xs ys len i j Hsum Hj Hji).
    reflexivity.
Qed.

Lemma prime469_selected_term_raw :
  forall len i j xs ys,
    (List.length xs + List.length ys <= len)%nat ->
    (j < len)%nat ->
    Prime469.zmul (nth j xs 0)
      (if Nat.leb j i
       then Prime469.zcanon (nth (i - j) ys 0)
       else Prime469.zcanon (nth (len + i - j) ys 0)) =
    Prime469.zcanon
      (if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
Proof.
  intros len i j xs ys Hsum Hj.
  destruct (Nat.leb j i) eqn:Hji.
  - unfold Prime469.zmul.
    rewrite Prime469.zcanon_mul_idemp_r.
    reflexivity.
  - apply Nat.leb_gt in Hji.
    unfold Prime469.zmul.
    rewrite Prime469.zcanon_mul_idemp_r.
    rewrite (convolution_wrap_term_zero xs ys len i j Hsum Hj Hji).
    reflexivity.
Qed.

Lemma prime181_selected_term :
  forall len i j xs ys,
    (List.length xs + List.length ys <= len)%nat ->
    (j < len)%nat ->
    Prime181.zmul (Prime181.zcanon (nth j xs 0))
      (if Nat.leb j i
       then Prime181.zcanon (nth (i - j) ys 0)
       else Prime181.zcanon (nth (len + i - j) ys 0)) =
    Prime181.zcanon
      (if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
Proof.
  intros len i j xs ys Hsum Hj.
  destruct (Nat.leb j i) eqn:Hji.
  - apply Nat.leb_le in Hji.
    unfold Prime181.zmul.
    rewrite Prime181.zcanon_mul.
    reflexivity.
  - apply Nat.leb_gt in Hji.
    unfold Prime181.zmul.
    rewrite Prime181.zcanon_mul.
    rewrite (convolution_wrap_term_zero xs ys len i j Hsum Hj Hji).
    reflexivity.
Qed.

Lemma prime181_selected_term_raw :
  forall len i j xs ys,
    (List.length xs + List.length ys <= len)%nat ->
    (j < len)%nat ->
    Prime181.zmul (nth j xs 0)
      (if Nat.leb j i
       then Prime181.zcanon (nth (i - j) ys 0)
       else Prime181.zcanon (nth (len + i - j) ys 0)) =
    Prime181.zcanon
      (if Nat.leb j i then nth j xs 0 * nth (i - j) ys 0 else 0).
Proof.
  intros len i j xs ys Hsum Hj.
  destruct (Nat.leb j i) eqn:Hji.
  - unfold Prime181.zmul.
    rewrite Prime181.zcanon_mul_idemp_r.
    reflexivity.
  - apply Nat.leb_gt in Hji.
    unfold Prime181.zmul.
    rewrite Prime181.zcanon_mul_idemp_r.
    rewrite (convolution_wrap_term_zero xs ys len i j Hsum Hj Hji).
    reflexivity.
Qed.

Lemma prime181_value_build_tree_input :
  forall k x i,
    (k <= supported_max_block_log)%nat ->
    (i < Prime181.pow2 (S (S (S k))))%nat ->
    (Z.of_nat (List.length x) <= Uint63.to_Z PArray.max_length)%Z ->
    Prime181.value
      (Prime181.input_get (S (S (S k)))
        (Prime181.unpack_tree8 k (build_tree181 k x)) i) =
    nth i (bigint_digits_z x) 0.
Proof.
  intros k x i Hk Hi Hlen.
  rewrite build_tree181_input_get by assumption.
  rewrite <- nth_bigint_digits_z.
  reflexivity.
Qed.

Lemma eqb_add_mod_left :
  forall len i l j,
    (0 < len)%nat ->
    (i < len)%nat ->
    (l <= i)%nat ->
    (j < len)%nat ->
    Nat.eqb i ((j + l) mod len) = Nat.eqb j (i - l).
Proof.
  intros len i l j Hlen Hi Hli Hj.
  destruct (Nat.eqb_spec j (i - l)) as [Heq|Hneq].
  - subst j.
    apply Nat.eqb_eq.
    rewrite Nat.sub_add by lia.
    rewrite Nat.mod_small by lia.
    reflexivity.
  - apply Nat.eqb_neq.
    intro Hmod.
    apply Hneq.
    destruct (lt_dec (j + l) len) as [Hsmall|Hwrap].
    + rewrite Nat.mod_small in Hmod by exact Hsmall.
      lia.
    + assert (Hlt2 : (j + l < len * 2)%nat) by lia.
      pose proof (Nat.div_mod (j + l) len ltac:(lia)) as Hdiv.
      assert (Hqge : (1 <= (j + l) / len)%nat).
      {
        apply Nat.div_le_lower_bound; lia.
      }
      assert (Hqlt : ((j + l) / len < 2)%nat).
      {
        apply Nat.Div0.div_lt_upper_bound; lia.
      }
      assert (Hq1 : ((j + l) / len = 1)%nat) by lia.
      rewrite Hq1 in Hdiv.
      rewrite <- Hmod in Hdiv.
      lia.
Qed.

Lemma eqb_add_mod_right :
  forall len i l j,
    (0 < len)%nat ->
    (i < len)%nat ->
    (i < l)%nat ->
    (l < len)%nat ->
    (j < len)%nat ->
    Nat.eqb i ((j + l) mod len) = Nat.eqb j (len + i - l).
Proof.
  intros len i l j Hlen Hi Hil Hl Hj.
  destruct (Nat.eqb_spec j (len + i - l)) as [Heq|Hneq].
  - subst j.
    apply Nat.eqb_eq.
    replace ((len + i - l + l)%nat) with (len + i)%nat by lia.
    rewrite <- Nat.Div0.add_mod_idemp_l.
    rewrite Nat.Div0.mod_same by lia.
    rewrite Nat.add_0_l.
    rewrite Nat.mod_small by lia.
    reflexivity.
  - apply Nat.eqb_neq.
    intro Hmod.
    apply Hneq.
    destruct (lt_dec (j + l) len) as [Hsmall|Hwrap].
    + rewrite Nat.mod_small in Hmod by exact Hsmall.
      lia.
    + assert (Hlt2 : (j + l < len * 2)%nat) by lia.
      pose proof (Nat.div_mod (j + l) len ltac:(lia)) as Hdiv.
      assert (Hqge : (1 <= (j + l) / len)%nat).
      {
        apply Nat.div_le_lower_bound; lia.
      }
      assert (Hqlt : ((j + l) / len < 2)%nat).
      {
        apply Nat.Div0.div_lt_upper_bound; lia.
      }
      assert (Hq1 : ((j + l) / len = 1)%nat) by lia.
      rewrite Hq1 in Hdiv.
      rewrite <- Hmod in Hdiv.
      lia.
Qed.

Lemma prime469_inner_sum_selected :
  forall len i l (f : nat -> Z),
    (0 < len)%nat ->
    (i < len)%nat ->
    (l < len)%nat ->
    Prime469.zsum len
      (fun j =>
         Prime469.zmul (Prime469.zcanon (f j))
           (Prime469Conv.delta_nat i ((j + l) mod len)%nat)) =
    if Nat.leb l i
    then Prime469.zcanon (f ((i - l)%nat))
    else Prime469.zcanon (f ((len + i - l)%nat)).
Proof.
  intros len i l f Hlen Hi Hl.
  destruct (Nat.leb_spec0 l i) as [Hli|Hli].
  - rewrite Prime469Conv.zsum_ext with
      (g := fun j =>
         Prime469.zcanon (if Nat.eqb j (i - l) then f j else 0)).
    2:{
      intros j Hj.
      unfold Prime469Conv.delta_nat.
      rewrite eqb_add_mod_left by lia.
      destruct (Nat.eqb j (i - l)) eqn:Heq.
      + rewrite Prime469Conv.zmul_1_r.
        apply Prime469.zcanon_idem.
      + rewrite Prime469Conv.zmul_0_r.
        unfold Prime469.zzero.
        reflexivity.
    }
    rewrite prime469_zsum_mod.
    rewrite zsum_nat_eqb_single by lia.
    destruct (Nat.leb l i); [reflexivity|lia].
  - rewrite Prime469Conv.zsum_ext with
      (g := fun j =>
         Prime469.zcanon (if Nat.eqb j ((len + i - l)%nat) then f j else 0)).
    2:{
      intros j Hj.
      unfold Prime469Conv.delta_nat.
      rewrite eqb_add_mod_right by lia.
      destruct (Nat.eqb j ((len + i - l)%nat)) eqn:Heq.
      + rewrite Prime469Conv.zmul_1_r.
        apply Prime469.zcanon_idem.
      + rewrite Prime469Conv.zmul_0_r.
        unfold Prime469.zzero.
        reflexivity.
    }
    rewrite prime469_zsum_mod.
    rewrite zsum_nat_eqb_single by lia.
    destruct (Nat.leb l i); [lia|reflexivity].
Qed.

Lemma prime181_inner_sum_selected :
  forall len i l (f : nat -> Z),
    (0 < len)%nat ->
    (i < len)%nat ->
    (l < len)%nat ->
    Prime181.zsum len
      (fun j =>
         Prime181.zmul (Prime181.zcanon (f j))
           (Prime181Conv.delta_nat i ((j + l) mod len)%nat)) =
    if Nat.leb l i
    then Prime181.zcanon (f ((i - l)%nat))
    else Prime181.zcanon (f ((len + i - l)%nat)).
Proof.
  intros len i l f Hlen Hi Hl.
  destruct (Nat.leb_spec0 l i) as [Hli|Hli].
  - rewrite Prime181Conv.zsum_ext with
      (g := fun j =>
         Prime181.zcanon (if Nat.eqb j (i - l) then f j else 0)).
    2:{
      intros j Hj.
      unfold Prime181Conv.delta_nat.
      rewrite eqb_add_mod_left by lia.
      destruct (Nat.eqb j (i - l)) eqn:Heq.
      + rewrite Prime181Conv.zmul_1_r.
        apply Prime181.zcanon_idem.
      + rewrite Prime181Conv.zmul_0_r.
        unfold Prime181.zzero.
        reflexivity.
    }
    rewrite prime181_zsum_mod.
    rewrite zsum_nat_eqb_single by lia.
    destruct (Nat.leb l i); [reflexivity|lia].
  - rewrite Prime181Conv.zsum_ext with
      (g := fun j =>
         Prime181.zcanon (if Nat.eqb j ((len + i - l)%nat) then f j else 0)).
    2:{
      intros j Hj.
      unfold Prime181Conv.delta_nat.
      rewrite eqb_add_mod_right by lia.
      destruct (Nat.eqb j ((len + i - l)%nat)) eqn:Heq.
      + rewrite Prime181Conv.zmul_1_r.
        apply Prime181.zcanon_idem.
      + rewrite Prime181Conv.zmul_0_r.
        unfold Prime181.zzero.
        reflexivity.
    }
    rewrite prime181_zsum_mod.
    rewrite zsum_nat_eqb_single by lia.
    destruct (Nat.leb l i); [lia|reflexivity].
Qed.

Lemma prime469_inner_sum_selected_raw :
  forall len i l (f : nat -> Z),
    (0 < len)%nat ->
    (i < len)%nat ->
    (l < len)%nat ->
    Prime469.zsum len
      (fun j =>
         Prime469.zmul (f j)
           (Prime469Conv.delta_nat i ((j + l) mod len)%nat)) =
    if Nat.leb l i
    then Prime469.zcanon (f ((i - l)%nat))
    else Prime469.zcanon (f ((len + i - l)%nat)).
Proof.
  intros len i l f Hlen Hi Hl.
  rewrite Prime469Conv.zsum_ext with
    (g := fun j =>
       Prime469.zmul (Prime469.zcanon (f j))
         (Prime469Conv.delta_nat i ((j + l) mod len)%nat)).
  2:{
    intros j Hj.
    unfold Prime469.zmul.
    rewrite Prime469.zcanon_mul_idemp_l.
    reflexivity.
  }
  apply prime469_inner_sum_selected; assumption.
Qed.

Lemma prime181_inner_sum_selected_raw :
  forall len i l (f : nat -> Z),
    (0 < len)%nat ->
    (i < len)%nat ->
    (l < len)%nat ->
    Prime181.zsum len
      (fun j =>
         Prime181.zmul (f j)
           (Prime181Conv.delta_nat i ((j + l) mod len)%nat)) =
    if Nat.leb l i
    then Prime181.zcanon (f ((i - l)%nat))
    else Prime181.zcanon (f ((len + i - l)%nat)).
Proof.
  intros len i l f Hlen Hi Hl.
  rewrite Prime181Conv.zsum_ext with
    (g := fun j =>
       Prime181.zmul (Prime181.zcanon (f j))
         (Prime181Conv.delta_nat i ((j + l) mod len)%nat)).
  2:{
    intros j Hj.
    unfold Prime181.zmul.
    rewrite Prime181.zcanon_mul_idemp_l.
    reflexivity.
  }
  apply prime181_inner_sum_selected; assumption.
Qed.

Lemma prime469_cyclic_convolution_bigint_digits :
  forall k a b i,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z ->
    (List.length (bigint_digits_z a) + List.length (bigint_digits_z b) <=
      Prime469.pow2 (S (S (S k))))%nat ->
    (i < Prime469.pow2 (S (S (S k))))%nat ->
    Prime469Conv.cyclic_convolution (S (S (S k)))
      (Prime469.unpack_tree8 k (build_tree469 k a))
      (Prime469.unpack_tree8 k (build_tree469 k b)) i =
    Prime469.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i).
Proof.
  intros k a b i Hk HlenA HlenB Hsum Hi.
  set (len := Prime469.pow2 (S (S (S k)))).
  unfold Prime469Conv.cyclic_convolution.
  subst len.
  rewrite Prime469Conv.zsum_ext with
    (g := fun j =>
       Prime469.zsum (Prime469.pow2 (S (S (S k))))
         (fun l =>
            Prime469.zmul
              (nth j (bigint_digits_z a) 0)
              (Prime469.zmul
                (nth l (bigint_digits_z b) 0)
                (Prime469Conv.delta_nat i
                  ((j + l) mod Prime469.pow2 (S (S (S k))))%nat)))).
  2:{
    intros j Hj.
    rewrite prime469_value_build_tree_input by assumption.
    apply Prime469Conv.zsum_ext.
    intros l Hl.
    rewrite prime469_value_build_tree_input by assumption.
    reflexivity.
  }
  rewrite Prime469Conv.zsum_ext with
    (g := fun j =>
       Prime469.zmul
         (nth j (bigint_digits_z a) 0)
         (Prime469.zsum (Prime469.pow2 (S (S (S k))))
           (fun l =>
              Prime469.zmul
                (nth l (bigint_digits_z b) 0)
                (Prime469Conv.delta_nat i
                  ((j + l) mod Prime469.pow2 (S (S (S k))))%nat)))).
  2:{
    intros j Hj.
    rewrite Prime469Conv.zsum_mul_const_l.
    reflexivity.
  }
  rewrite Prime469Conv.zsum_ext with
    (g := fun j =>
       Prime469.zmul
         (nth j (bigint_digits_z a) 0)
         (if Nat.leb j i
          then Prime469.zcanon (nth (i - j) (bigint_digits_z b) 0)
          else Prime469.zcanon
            (nth (Prime469.pow2 (S (S (S k))) + i - j) (bigint_digits_z b) 0))).
  2:{
    intros j Hj.
    rewrite Prime469Conv.zsum_ext with
      (g := fun l =>
         Prime469.zmul (nth l (bigint_digits_z b) 0)
           (Prime469Conv.delta_nat i
             ((l + j) mod Prime469.pow2 (S (S (S k))))%nat)).
    2:{
      intros l Hl.
      f_equal.
      rewrite Nat.add_comm.
      reflexivity.
    }
    assert (Hinner :
      Prime469.zsum (Prime469.pow2 (S (S (S k))))
        (fun l =>
           Prime469.zmul (nth l (bigint_digits_z b) 0)
             (Prime469Conv.delta_nat i
               ((l + j) mod Prime469.pow2 (S (S (S k))))%nat)) =
      if Nat.leb j i
      then Prime469.zcanon (nth (i - j) (bigint_digits_z b) 0)
      else Prime469.zcanon
        (nth (Prime469.pow2 (S (S (S k))) + i - j) (bigint_digits_z b) 0)).
    {
      apply (prime469_inner_sum_selected_raw
        (Prime469.pow2 (S (S (S k)))) i j
        (fun l => nth l (bigint_digits_z b) 0)).
      - apply Prime469.pow2_pos.
      - exact Hi.
      - exact Hj.
    }
    setoid_rewrite Hinner.
    reflexivity.
  }
  rewrite Prime469Conv.zsum_ext with
    (g := fun j =>
       Prime469.zcanon
         (if Nat.leb j i
          then nth j (bigint_digits_z a) 0 * nth (i - j) (bigint_digits_z b) 0
          else 0)).
  2:{
    intros j Hj.
    apply prime469_selected_term_raw; assumption.
  }
  rewrite prime469_zsum_mod.
  f_equal.
  symmetry.
  apply convolution_coeff_zsum_nat_len.
  apply Nat.le_succ_l.
  exact Hi.
Qed.

Lemma prime181_cyclic_convolution_bigint_digits :
  forall k a b i,
    (k <= supported_max_block_log)%nat ->
    (Z.of_nat (List.length a) <= Uint63.to_Z PArray.max_length)%Z ->
    (Z.of_nat (List.length b) <= Uint63.to_Z PArray.max_length)%Z ->
    (List.length (bigint_digits_z a) + List.length (bigint_digits_z b) <=
      Prime181.pow2 (S (S (S k))))%nat ->
    (i < Prime181.pow2 (S (S (S k))))%nat ->
    Prime181Conv.cyclic_convolution (S (S (S k)))
      (Prime181.unpack_tree8 k (build_tree181 k a))
      (Prime181.unpack_tree8 k (build_tree181 k b)) i =
    Prime181.zcanon (convolution_coeff (bigint_digits_z a) (bigint_digits_z b) i).
Proof.
  intros k a b i Hk HlenA HlenB Hsum Hi.
  set (len := Prime181.pow2 (S (S (S k)))).
  unfold Prime181Conv.cyclic_convolution.
  subst len.
  rewrite Prime181Conv.zsum_ext with
    (g := fun j =>
       Prime181.zsum (Prime181.pow2 (S (S (S k))))
         (fun l =>
            Prime181.zmul
              (nth j (bigint_digits_z a) 0)
              (Prime181.zmul
                (nth l (bigint_digits_z b) 0)
                (Prime181Conv.delta_nat i
                  ((j + l) mod Prime181.pow2 (S (S (S k))))%nat)))).
  2:{
    intros j Hj.
    rewrite prime181_value_build_tree_input by assumption.
    apply Prime181Conv.zsum_ext.
    intros l Hl.
    rewrite prime181_value_build_tree_input by assumption.
    reflexivity.
  }
  rewrite Prime181Conv.zsum_ext with
    (g := fun j =>
       Prime181.zmul
         (nth j (bigint_digits_z a) 0)
         (Prime181.zsum (Prime181.pow2 (S (S (S k))))
           (fun l =>
              Prime181.zmul
                (nth l (bigint_digits_z b) 0)
                (Prime181Conv.delta_nat i
                  ((j + l) mod Prime181.pow2 (S (S (S k))))%nat)))).
  2:{
    intros j Hj.
    rewrite Prime181Conv.zsum_mul_const_l.
    reflexivity.
  }
  rewrite Prime181Conv.zsum_ext with
    (g := fun j =>
       Prime181.zmul
         (nth j (bigint_digits_z a) 0)
         (if Nat.leb j i
          then Prime181.zcanon (nth (i - j) (bigint_digits_z b) 0)
          else Prime181.zcanon
            (nth (Prime181.pow2 (S (S (S k))) + i - j) (bigint_digits_z b) 0))).
  2:{
    intros j Hj.
    rewrite Prime181Conv.zsum_ext with
      (g := fun l =>
         Prime181.zmul (nth l (bigint_digits_z b) 0)
           (Prime181Conv.delta_nat i
             ((l + j) mod Prime181.pow2 (S (S (S k))))%nat)).
    2:{
      intros l Hl.
      f_equal.
      rewrite Nat.add_comm.
      reflexivity.
    }
    assert (Hinner :
      Prime181.zsum (Prime181.pow2 (S (S (S k))))
        (fun l =>
           Prime181.zmul (nth l (bigint_digits_z b) 0)
             (Prime181Conv.delta_nat i
               ((l + j) mod Prime181.pow2 (S (S (S k))))%nat)) =
      if Nat.leb j i
      then Prime181.zcanon (nth (i - j) (bigint_digits_z b) 0)
      else Prime181.zcanon
        (nth (Prime181.pow2 (S (S (S k))) + i - j) (bigint_digits_z b) 0)).
    {
      apply (prime181_inner_sum_selected_raw
        (Prime181.pow2 (S (S (S k)))) i j
        (fun l => nth l (bigint_digits_z b) 0)).
      - apply Prime181.pow2_pos.
      - exact Hi.
      - exact Hj.
    }
    setoid_rewrite Hinner.
    reflexivity.
  }
  rewrite Prime181Conv.zsum_ext with
    (g := fun j =>
       Prime181.zcanon
         (if Nat.leb j i
          then nth j (bigint_digits_z a) 0 * nth (i - j) (bigint_digits_z b) 0
          else 0)).
  2:{
    intros j Hj.
    apply prime181_selected_term_raw; assumption.
  }
  rewrite prime181_zsum_mod.
  f_equal.
  symmetry.
  apply convolution_coeff_zsum_nat_len.
  apply Nat.le_succ_l.
  exact Hi.
Qed.
