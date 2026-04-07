From Coq Require Import ZArith Lia.
Require Import BigInt.NTTTree BigInt.NTTConvolution.

Local Open Scope Z_scope.

Module TreeNTTSpectral (C : NTTBaseCfg).
  Module Conv := TreeNTTConvolution(C).
  Module T := Conv.T.
  Import T Conv.

  Definition zminus_one : Z := zsub zzero zone.

  Lemma zcanon_zone :
    zcanon zone = zone.
  Proof.
    unfold zone.
    apply zcanon_small.
    split.
    - lia.
    - destruct C.modulus_range as [Hmod _].
      exact Hmod.
  Qed.

  Lemma zpow_add :
    forall x a b,
      zpow x (a + b)%nat = zmul (zpow x a) (zpow x b).
  Proof.
    intros x a b.
    induction b as [|b IH].
    - simpl.
      rewrite Nat.add_0_r.
      rewrite Conv.zmul_1_r.
      symmetry.
      apply zcanon_small.
      apply zpow_range.
    - simpl.
      rewrite Nat.add_succ_r.
      simpl.
      rewrite IH.
      rewrite zmul_assoc.
      reflexivity.
  Qed.

  Lemma zpow_mul :
    forall x a b,
      zpow x (a * b)%nat = zpow (zpow x a) b.
  Proof.
    intros x a b.
    induction b as [|b IH].
    - simpl.
      rewrite Nat.mul_0_r.
      reflexivity.
    - simpl.
      rewrite Nat.mul_succ_r.
      rewrite zpow_add.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma zpow_1 :
    forall x,
      zpow x 1%nat = zcanon x.
  Proof.
    intro x.
    simpl.
    rewrite zmul_1_l.
    reflexivity.
  Qed.

  Lemma zmul_neg_one_r :
    forall x,
      zmul x zminus_one = zsub zzero x.
  Proof.
    intro x.
    unfold zmul, zminus_one, zsub, zzero, zone.
    rewrite zcanon_mul_idemp_r.
    replace (x * (0 - 1))%Z with (0 - x)%Z by lia.
    reflexivity.
  Qed.

  Lemma zmul_neg_one_l :
    forall x,
      zmul zminus_one x = zsub zzero x.
  Proof.
    intro x.
    rewrite zmul_comm.
    apply zmul_neg_one_r.
  Qed.

  Lemma zsub_eq_add_neg :
    forall x y,
      zsub x y = zadd x (zmul y zminus_one).
  Proof.
    intros x y.
    rewrite zmul_neg_one_r.
    unfold zsub, zadd, zzero.
    rewrite zcanon_add_idemp_r.
    replace (x + (0 - y))%Z with (x - y)%Z by lia.
    reflexivity.
  Qed.

  Lemma zmul_shuffle3 :
    forall a b c,
      zmul a (zmul b c) = zmul c (zmul a b).
  Proof.
    intros a b c.
    rewrite zmul_assoc.
    rewrite (zmul_comm (zmul a b) c).
    reflexivity.
  Qed.

  Lemma zmul_shuffle4 :
    forall a b c d,
      zmul a (zmul b (zmul c d)) = zmul d (zmul a (zmul b c)).
  Proof.
    intros a b c d.
    rewrite zmul_assoc.
    rewrite zmul_assoc.
    rewrite (zmul_comm (zmul (zmul a b) c) d).
    repeat rewrite <- zmul_assoc.
    reflexivity.
  Qed.

  Lemma zmul_perm4 :
    forall a b c d,
      zmul a (zmul b (zmul c d)) = zmul c (zmul (zmul d b) a).
  Proof.
    intros a b c d.
    rewrite zmul_assoc.
    rewrite (zmul_comm (zmul a b) (zmul c d)).
    repeat rewrite <- zmul_assoc.
    rewrite (zmul_comm a b).
    rewrite zmul_assoc.
    reflexivity.
  Qed.

  Lemma zminus_one_sq :
    zmul zminus_one zminus_one = zone.
  Proof.
    unfold zminus_one, zsub, zmul, zzero, zone.
    rewrite zcanon_mul.
    change ((0 - 1) * (0 - 1))%Z with 1%Z.
    unfold zcanon.
    apply Z.mod_small.
    split.
    - lia.
    - destruct C.modulus_range as [Hmod _].
      exact Hmod.
  Qed.

  Lemma zpow_zone :
    forall n,
      zpow zone n = zone.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - simpl.
      rewrite IH.
      rewrite zmul_1_l.
      apply zcanon_zone.
  Qed.

  Lemma zpow_canon :
    forall x n,
      zcanon (zpow x n) = zpow x n.
  Proof.
    intros x n.
    apply zcanon_small.
    apply zpow_range.
  Qed.

  Lemma zpow_zminus_one_two :
    zpow zminus_one 2%nat = zone.
  Proof.
    simpl.
    rewrite zmul_1_l.
    replace (zcanon zminus_one) with zminus_one.
    2:{
      unfold zminus_one.
      symmetry.
      apply zcanon_idem.
    }
    apply zminus_one_sq.
  Qed.

  Lemma zpow_zminus_one_even :
    forall m,
      zpow zminus_one (2 * m)%nat = zone.
  Proof.
    intro m.
    rewrite zpow_mul.
    rewrite zpow_zminus_one_two.
    apply zpow_zone.
  Qed.

  Lemma zpow_zminus_one_odd :
    forall m,
      zpow zminus_one (S (2 * m))%nat = zminus_one.
  Proof.
    intro m.
    replace (S (2 * m))%nat with ((2 * m) + 1)%nat by lia.
    rewrite zpow_add.
    rewrite zpow_zminus_one_even.
    replace (zpow zminus_one 1%nat) with zminus_one.
    2:{
      unfold zminus_one, zsub, zzero, zone.
      simpl.
      rewrite zmul_1_l.
      symmetry.
      apply zcanon_idem.
    }
    rewrite zmul_1_l.
    replace (zcanon zminus_one) with zminus_one.
    2:{
      unfold zminus_one.
      symmetry.
      apply zcanon_idem.
    }
    reflexivity.
  Qed.

  Lemma zsum_canon :
    forall n (f : nat -> Z),
      zcanon (zsum n f) = zsum n f.
  Proof.
    induction n as [|n IH]; intro f.
    - simpl.
      apply zcanon_0.
    - simpl.
      unfold zadd.
      rewrite zcanon_idem.
      reflexivity.
  Qed.

  Lemma input_get_even :
    forall n (l r : tree int n) j,
      input_get (S n) (l, r) (2 * j)%nat = input_get n l j.
  Proof.
    intros n l r j.
    cbn [input_get].
    replace (Nat.even (2 * j)) with true.
    2:{
      symmetry.
      apply Nat.even_spec.
      exists j.
      reflexivity.
    }
    replace (Nat.div2 (2 * j)) with j by (symmetry; apply Nat.div2_double).
    reflexivity.
  Qed.

  Lemma input_get_odd :
    forall n (l r : tree int n) j,
      input_get (S n) (l, r) (S (2 * j))%nat = input_get n r j.
  Proof.
    intros n l r j.
    cbn [input_get].
    replace (Nat.even (S (2 * j))) with false.
    2:{
      destruct (Nat.even (S (2 * j))) eqn:Hev.
      - apply Nat.even_spec in Hev.
        destruct Hev as [m Hm].
        lia.
      - reflexivity.
    }
    replace (Nat.div2 (S (2 * j))) with j by (symmetry; apply Nat.div2_succ_double).
    reflexivity.
  Qed.

  Lemma zsum_split_even_odd :
    forall m (f : nat -> Z),
      zsum (m + m)%nat f =
      zsum m (fun j => zadd (f (2 * j)%nat) (f (S (2 * j)%nat))).
  Proof.
    induction m as [|m IH]; intro f.
    - reflexivity.
    - replace (S m + S m)%nat with (S (S (m + m)))%nat by lia.
      simpl.
      replace (m + (m + 0))%nat with (m + m)%nat by lia.
      rewrite IH.
      replace (2 * m)%nat with (m + m)%nat by lia.
      replace (S (2 * m))%nat with (S (m + m))%nat by lia.
      rewrite <- zadd_assoc.
      reflexivity.
  Qed.

  Lemma zsum_split_at :
    forall m n (f : nat -> Z),
      zsum (m + n)%nat f =
      zadd (zsum m f) (zsum n (fun k => f (k + m)%nat)).
  Proof.
    intros m n f.
    induction n as [|n IH].
    - rewrite Nat.add_0_r.
      simpl.
      rewrite Conv.zadd_0_r.
      symmetry.
      apply zsum_canon.
    - rewrite Nat.add_succ_r.
      simpl.
      rewrite IH.
      replace (n + m)%nat with (m + n)%nat by lia.
      rewrite zadd_assoc.
      reflexivity.
  Qed.

  Lemma output_get_left :
    forall n (l r : tree int n) k,
      (k < pow2 n)%nat ->
      output_get (S n) (l, r) k = output_get n l k.
  Proof.
    intros n l r k Hk.
    simpl.
    destruct (Nat.ltb_spec0 k (pow2 n)) as [Hlt|Hge].
    - reflexivity.
    - lia.
  Qed.

  Lemma output_get_right :
    forall n (l r : tree int n) k,
      (k < pow2 n)%nat ->
      output_get (S n) (l, r) (k + pow2 n)%nat = output_get n r k.
  Proof.
    intros n l r k Hk.
    simpl.
    destruct (Nat.ltb_spec0 (k + pow2 n) (pow2 n)) as [Hlt|Hge].
    - lia.
    - replace (Nat.sub (k + pow2 n) (pow2 n)) with k by lia.
      reflexivity.
  Qed.

  Section ClosedForm.
    Variable rootf : nat -> int.

    Hypothesis rootf_square :
      forall n,
        zpow (value (rootf (S n))) 2%nat = value (rootf n).

    Hypothesis rootf_half_neg :
      forall n,
        zpow (value (rootf (S n))) (pow2 n) = zminus_one.

    Lemma rootf_even_power :
      forall n m,
        zpow (value (rootf (S n))) (2 * m)%nat =
        zpow (value (rootf n)) m.
    Proof.
      intros n m.
      rewrite zpow_mul.
      rewrite rootf_square.
      reflexivity.
    Qed.

    Lemma rootf_period_even :
      forall n j,
        zpow (value (rootf (S n))) (2 * (j * pow2 n))%nat = zone.
    Proof.
      intros n j.
      replace (2 * (j * pow2 n))%nat with ((pow2 n) * (2 * j))%nat by lia.
      rewrite zpow_mul.
      rewrite rootf_half_neg.
      apply zpow_zminus_one_even.
    Qed.

    Lemma rootf_period_odd :
      forall n j,
        zpow (value (rootf (S n))) ((S (2 * j)) * pow2 n)%nat = zminus_one.
    Proof.
      intros n j.
      replace ((S (2 * j)) * pow2 n)%nat with ((pow2 n) * (S (2 * j)))%nat by lia.
      rewrite zpow_mul.
      rewrite rootf_half_neg.
      apply zpow_zminus_one_odd.
    Qed.

    Theorem dft_with_closed_form :
      forall n (t : tree int n) k,
        canonical_tree n t ->
        (k < pow2 n)%nat ->
        dft_with rootf n t k =
        zsum (pow2 n)
          (fun j =>
             zmul (value (input_get n t j))
               (zpow (value (rootf n)) ((j * k)%nat))).
    Proof.
      induction n as [|n IH]; intros t k Ht Hk.
      - apply Nat.lt_1_r in Hk.
        subst k.
        simpl.
        rewrite Conv.zmul_1_r.
        rewrite zadd_0_l.
        rewrite zcanon_idem.
        symmetry.
        apply zcanon_small.
        exact Ht.
      - destruct t as [l r].
        simpl in Ht.
        destruct Ht as [Hl Hr].
        cbn [dft_with].
        destruct (Nat.ltb_spec0 k (pow2 n)) as [Hlt|Hge].
        + rewrite pow2_succ.
          rewrite zsum_split_even_odd.
          rewrite zsum_add_distr.
          rewrite zsum_ext with
            (g := fun j =>
               zmul (value (input_get n l j))
                 (zpow (value (rootf n)) ((j * k)%nat))).
          2:{
            intros j Hj.
            cbn [input_get].
            replace (Nat.even (2 * j)) with true.
            2:{
              symmetry.
              apply Nat.even_spec.
              exists j.
              reflexivity.
            }
            replace (Nat.div2 (2 * j)) with j by (symmetry; apply Nat.div2_double).
            replace ((2 * j * k)%nat) with (2 * (j * k))%nat by lia.
            apply f_equal.
            apply rootf_even_power.
          }
          replace
            (zsum (pow2 n)
               (fun j =>
                  zmul (value (input_get (S n) (l, r) (S (2 * j))%nat))
                    (zpow (value (rootf (S n))) ((S (2 * j) * k)%nat))))
            with
            (zsum (pow2 n)
               (fun j =>
                  zmul (zpow (value (rootf (S n))) k)
                    (zmul (value (input_get n r j))
                      (zpow (value (rootf n)) ((j * k)%nat))))).
          2:{
            apply zsum_ext.
            intros j Hj.
            cbn [input_get].
            replace (Nat.even (S (2 * j))) with false.
            2:{
              destruct (Nat.even (S (2 * j))) eqn:Hev.
              - apply Nat.even_spec in Hev.
                destruct Hev as [m Hm].
                lia.
              - reflexivity.
            }
            replace (Nat.div2 (S (2 * j))) with j by (symmetry; apply Nat.div2_succ_double).
            replace (((S (2 * j)) * k)%nat) with ((2 * (j * k) + k)%nat) by lia.
            replace
              (zpow (value (rootf (S n))) (2 * (j * k) + k))
              with
              (zmul (zpow (value (rootf (S n))) (2 * (j * k)))
                 (zpow (value (rootf (S n))) k))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (rootf (S n))) (2 * (j * k)))
              with (zpow (value (rootf n)) (j * k))
              by (symmetry; apply rootf_even_power).
            rewrite zmul_assoc.
            rewrite (zmul_comm
                       (zpow (value (rootf (S n))) k)
                       (value (input_get n r j))).
            rewrite <- zmul_assoc.
            f_equal.
            rewrite (zmul_comm
                       (zpow (value (rootf (S n))) k)
                       (zpow (value (rootf n)) (j * k))).
            reflexivity.
          }
          rewrite <- zsum_mul_const_l.
          rewrite <- (IH l k Hl Hlt).
          rewrite <- (IH r k Hr Hlt).
          reflexivity.
        + set (u := Nat.sub k (pow2 n)).
          assert (Hu : (u < pow2 n)%nat).
          {
            subst u.
            rewrite pow2_succ in Hk.
            lia.
          }
          assert (Hk_eq : (k = u + pow2 n)%nat).
          {
            subst u.
            lia.
          }
          rewrite Hk_eq.
          rewrite pow2_succ.
          rewrite zsum_split_even_odd.
          rewrite zsum_add_distr.
          rewrite zsum_ext with
            (g := fun j =>
               zmul (value (input_get n l j))
                 (zpow (value (rootf n)) ((j * u)%nat))).
          2:{
            intros j Hj.
            cbn [input_get].
            replace (Nat.even (2 * j)) with true.
            2:{
              symmetry.
              apply Nat.even_spec.
              exists j.
              reflexivity.
            }
            replace (Nat.div2 (2 * j)) with j by (symmetry; apply Nat.div2_double).
            replace ((2 * j * (u + pow2 n))%nat)
              with ((2 * (j * u) + 2 * (j * pow2 n))%nat) by lia.
            replace
              (zpow (value (rootf (S n))) (2 * (j * u) + 2 * (j * pow2 n)))
              with
              (zmul (zpow (value (rootf (S n))) (2 * (j * u)))
                 (zpow (value (rootf (S n))) (2 * (j * pow2 n))))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (rootf (S n))) (2 * (j * u)))
              with (zpow (value (rootf n)) (j * u))
              by (symmetry; apply rootf_even_power).
            replace
              (zpow (value (rootf (S n))) (2 * (j * pow2 n)))
              with zone
              by (symmetry; apply rootf_period_even).
            rewrite Conv.zmul_1_r.
            rewrite zpow_canon.
            reflexivity.
          }
          replace
            (zsum (pow2 n)
               (fun j =>
                  zmul (value (input_get (S n) (l, r) (S (2 * j))%nat))
                    (zpow (value (rootf (S n))) ((S (2 * j) * (u + pow2 n))%nat))))
            with
            (zsum (pow2 n)
               (fun j =>
                  zmul zminus_one
                    (zmul (zpow (value (rootf (S n))) u)
                      (zmul (value (input_get n r j))
                        (zpow (value (rootf n)) ((j * u)%nat)))))).
          2:{
            apply zsum_ext.
            intros j Hj.
            cbn [input_get].
            replace (Nat.even (S (2 * j))) with false.
            2:{
              destruct (Nat.even (S (2 * j))) eqn:Hev.
              - apply Nat.even_spec in Hev.
                destruct Hev as [m Hm].
                lia.
              - reflexivity.
            }
            replace (Nat.div2 (S (2 * j))) with j by (symmetry; apply Nat.div2_succ_double).
            replace (((S (2 * j)) * (u + pow2 n))%nat)
              with (((2 * (j * u) + u) + ((S (2 * j)) * pow2 n))%nat) by lia.
            replace
              (zpow (value (rootf (S n)))
                 ((2 * (j * u) + u) + (S (2 * j) * pow2 n)))
              with
              (zmul
                 (zpow (value (rootf (S n))) (2 * (j * u) + u))
                 (zpow (value (rootf (S n))) (S (2 * j) * pow2 n)))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (rootf (S n))) (2 * (j * u) + u))
              with
              (zmul (zpow (value (rootf (S n))) (2 * (j * u)))
                 (zpow (value (rootf (S n))) u))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (rootf (S n))) (2 * (j * u)))
              with (zpow (value (rootf n)) (j * u))
              by (symmetry; apply rootf_even_power).
            replace
              (zpow (value (rootf (S n))) (S (2 * j) * pow2 n))
              with zminus_one
              by (symmetry; apply rootf_period_odd).
            apply zmul_perm4.
          }
          rewrite <- zsum_mul_const_l.
          rewrite <- zsum_mul_const_l.
          rewrite <- (IH l u Hl Hu).
          rewrite <- (IH r u Hr Hu).
          rewrite (zmul_comm zminus_one
                     (zmul (zpow (value (rootf (S n))) u) (dft_with rootf n r u))).
          rewrite <- zsub_eq_add_neg.
          reflexivity.
    Qed.
  End ClosedForm.

  Lemma dft_with_root_eq :
    forall n (t : tree int n) k,
      dft_with root n t k = dft n t k.
  Proof.
    induction n as [|n IH]; intros t k.
    - reflexivity.
    - destruct t as [l r].
      simpl.
      destruct (Nat.ltb k (pow2 n)).
      + rewrite IH.
        rewrite IH.
        reflexivity.
      + rewrite IH.
        rewrite IH.
        reflexivity.
  Qed.

  Section ForwardFast.
    Hypothesis root_square :
      forall n,
        zpow (value (root (S n))) 2%nat = value (root n).

    Hypothesis root_half_neg :
      forall n,
        zpow (value (root (S n))) (pow2 n) = zminus_one.

    Theorem ntt_fast_closed_form :
      forall n (t : tree int n) k,
        canonical_tree n t ->
        (k < pow2 n)%nat ->
        value (output_get n (ntt_fast n t) k) =
        zsum (pow2 n)
          (fun j =>
             zmul (value (input_get n t j))
               (zpow (value (root n)) ((j * k)%nat))).
    Proof.
      intros n t k Ht Hk.
      rewrite ntt_fast_correct by assumption.
      rewrite <- dft_with_root_eq.
      apply dft_with_closed_form; assumption.
    Qed.
  End ForwardFast.

  Section InverseFast.
    Hypothesis inv_root_square :
      forall n,
        zpow (value (inv_root (S n))) 2%nat = value (inv_root n).

    Hypothesis inv_root_half_neg :
      forall n,
        zpow (value (inv_root (S n))) (pow2 n) = zminus_one.

    Lemma inv_root_even_power :
      forall n m,
        zpow (value (inv_root (S n))) (2 * m)%nat =
        zpow (value (inv_root n)) m.
    Proof.
      intros n m.
      rewrite zpow_mul.
      rewrite inv_root_square.
      reflexivity.
    Qed.

    Lemma inv_root_period_even :
      forall n j,
        zpow (value (inv_root (S n))) (2 * (j * pow2 n))%nat = zone.
    Proof.
      intros n j.
      replace (2 * (j * pow2 n))%nat with ((pow2 n) * (2 * j))%nat by lia.
      rewrite zpow_mul.
      rewrite inv_root_half_neg.
      apply zpow_zminus_one_even.
    Qed.

    Lemma inv_root_period_odd :
      forall n j,
        zpow (value (inv_root (S n))) ((S (2 * j)) * pow2 n)%nat = zminus_one.
    Proof.
      intros n j.
      replace ((S (2 * j)) * pow2 n)%nat with ((pow2 n) * (S (2 * j)))%nat by lia.
      rewrite zpow_mul.
      rewrite inv_root_half_neg.
      apply zpow_zminus_one_odd.
    Qed.

    Theorem idft_dif_raw_closed_form :
      forall n (t : tree int n) i,
        canonical_tree n t ->
        (i < pow2 n)%nat ->
        idft_dif_raw n t i =
        zsum (pow2 n)
          (fun k =>
             zmul (value (output_get n t k))
               (zpow (value (inv_root n)) ((i * k)%nat))).
    Proof.
      induction n as [|n IH]; intros t i Ht Hi.
      - apply Nat.lt_1_r in Hi.
        subst i.
        simpl.
        rewrite Conv.zmul_1_r.
        rewrite zadd_0_l.
        rewrite zcanon_idem.
        symmetry.
        apply zcanon_small.
        exact Ht.
      - destruct t as [l r].
        simpl in Ht.
        destruct Ht as [Hl Hr].
        cbn [idft_dif_raw].
        destruct (Nat.even i) eqn:Hev.
        + set (j := Nat.div2 i).
          assert (Heq : (i = 2 * j)%nat).
          {
            subst j.
            apply Nat.even_spec in Hev.
            rewrite <- Nat.double_twice.
            apply Nat.Even_double.
            exact Hev.
          }
          assert (Hj : (j < pow2 n)%nat).
          {
            subst j.
            rewrite pow2_succ in Hi.
            rewrite Heq in Hi.
            lia.
          }
          rewrite (IH (zip_tree n add_mod l r) j).
          2:{ apply canonical_zip_add; assumption. }
          2:{ exact Hj. }
          subst j.
          rewrite zsum_ext with
            (g := fun k =>
               zadd
                 (zmul (value (output_get n l k))
                   (zpow (value (inv_root n)) (((Nat.div2 i) * k)%nat)))
                 (zmul (value (output_get n r k))
                   (zpow (value (inv_root n)) (((Nat.div2 i) * k)%nat)))).
          2:{
            intros k Hk.
            rewrite output_get_zip_tree by exact Hk.
            rewrite value_add_mod.
            rewrite zmul_add_distr_r.
            reflexivity.
          }
          rewrite zsum_add_distr.
          rewrite Heq in *.
          replace (Nat.div2 (2 * Nat.div2 i)) with (Nat.div2 i) in * by
            (symmetry; apply Nat.div2_double).
          rewrite pow2_succ.
          rewrite (zsum_split_at (pow2 n) (pow2 n)
                     (fun k =>
                        zmul (value (output_get (S n) (l, r) k))
                          (zpow (value (inv_root (S n)))
                             ((2 * Nat.div2 i * k)%nat)))).
          apply f_equal2.
          * apply zsum_ext.
            intros k Hk.
            rewrite output_get_left by exact Hk.
            replace ((2 * Nat.div2 i * k)%nat) with (2 * (Nat.div2 i * k))%nat by lia.
            rewrite inv_root_even_power.
            reflexivity.
          * apply zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            rewrite output_get_right by exact Hk.
            replace ((2 * Nat.div2 i) * (k + pow2 n))%nat
              with (2 * (Nat.div2 i * k) + 2 * (Nat.div2 i * pow2 n))%nat by lia.
            rewrite (zpow_add (value (inv_root (S n)))
                        (2 * (Nat.div2 i * k)) (2 * (Nat.div2 i * pow2 n))).
            rewrite inv_root_even_power.
            rewrite inv_root_period_even.
            rewrite Conv.zmul_1_r.
            rewrite zpow_canon.
            reflexivity.
        + set (j := Nat.div2 i).
          assert (Heq : (i = S (2 * j))%nat).
          {
            subst j.
            assert (Hodd : Nat.odd i = true).
            {
              rewrite <- Nat.negb_even.
              rewrite Hev.
              reflexivity.
            }
            apply Nat.odd_spec in Hodd.
            rewrite <- Nat.double_twice.
            apply Nat.Odd_double.
            exact Hodd.
          }
          assert (Hj : (j < pow2 n)%nat).
          {
            subst j.
            rewrite pow2_succ in Hi.
            rewrite Heq in Hi.
            lia.
          }
          rewrite (IH (twiddle_tree n (inv_root (S n)) (zip_tree n sub_mod l r)) j).
          2:{
            apply canonical_twiddle_from.
            apply canonical_zip_sub; assumption.
          }
          2:{ exact Hj. }
          subst j.
          rewrite zsum_ext with
            (g := fun k =>
               zmul
                 (zmul
                   (value (output_get n (zip_tree n sub_mod l r) k))
                   (zpow (value (inv_root (S n))) k))
                 (zpow (value (inv_root n)) ((Nat.div2 i * k)%nat))).
          2:{
            intros k Hk.
            unfold twiddle_tree.
            rewrite output_get_twiddle_from by exact Hk.
            rewrite value_mul_mod.
            rewrite value_pow_mod.
            replace (0 + k)%nat with k by lia.
            rewrite (zmul_comm
                       (zpow (value (inv_root (S n))) k)
                       (value (output_get n (zip_tree n sub_mod l r) k))).
            reflexivity.
          }
          rewrite zsum_ext with
            (g := fun k =>
               zmul
                 (zsub (value (output_get n l k)) (value (output_get n r k)))
                 (zmul (zpow (value (inv_root (S n))) k)
                   (zpow (value (inv_root n)) ((Nat.div2 i * k)%nat)))).
          2:{
            intros k Hk.
            rewrite output_get_zip_tree by exact Hk.
            rewrite value_sub_mod.
            repeat rewrite <- zmul_assoc.
            reflexivity.
          }
          rewrite zsum_ext with
            (g := fun k =>
               zadd
                 (zmul (value (output_get n l k))
                   (zmul (zpow (value (inv_root (S n))) k)
                     (zpow (value (inv_root n)) ((Nat.div2 i * k)%nat))))
                 (zmul (zmul (value (output_get n r k)) zminus_one)
                   (zmul (zpow (value (inv_root (S n))) k)
                     (zpow (value (inv_root n)) ((Nat.div2 i * k)%nat))))).
          2:{
            intros k Hk.
            rewrite zsub_eq_add_neg.
            rewrite zmul_add_distr_r.
            reflexivity.
          }
          rewrite zsum_add_distr.
          rewrite Heq in *.
          replace (Nat.div2 (S (2 * Nat.div2 i))) with (Nat.div2 i) in * by
            (symmetry; apply Nat.div2_succ_double).
          rewrite pow2_succ.
          rewrite (zsum_split_at (pow2 n) (pow2 n)
                     (fun k =>
                        zmul (value (output_get (S n) (l, r) k))
                          (zpow (value (inv_root (S n)))
                             ((S (2 * Nat.div2 i) * k)%nat)))).
          apply f_equal2.
          * apply zsum_ext.
            intros k Hk.
            rewrite output_get_left by exact Hk.
            replace ((S (2 * Nat.div2 i) * k)%nat)
              with ((k + 2 * (Nat.div2 i * k))%nat) by lia.
            rewrite zpow_add.
            rewrite inv_root_even_power.
            rewrite zmul_assoc.
            reflexivity.
          * apply zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            rewrite output_get_right by exact Hk.
            replace ((S (2 * Nat.div2 i)) * (k + pow2 n))%nat
              with ((k + 2 * (Nat.div2 i * k)) + (S (2 * Nat.div2 i) * pow2 n))%nat by lia.
            rewrite zpow_add.
            rewrite zpow_add.
            rewrite inv_root_even_power.
            rewrite inv_root_period_odd.
            rewrite <- zmul_assoc.
            rewrite <- zmul_assoc.
            rewrite (zmul_comm
                       zminus_one
                       (zmul
                         (zpow (value (inv_root (S n))) k)
                         (zpow (value (inv_root n)) (Nat.div2 i * k)))).
            replace
              (zmul (value (output_get n r k))
                 (zmul (zpow (value (inv_root (S n))) k)
                    (zmul (zpow (value (inv_root n)) (Nat.div2 i * k)) zminus_one)))
              with
                (zmul (value (output_get n r k))
                   (zmul
                      (zmul (zpow (value (inv_root (S n))) k)
                         (zpow (value (inv_root n)) (Nat.div2 i * k)))
                      zminus_one)).
            2:{
              rewrite (zmul_assoc
                         (zpow (value (inv_root (S n))) k)
                         (zpow (value (inv_root n)) (Nat.div2 i * k))
                         zminus_one).
              reflexivity.
            }
            rewrite zmul_assoc.
            reflexivity.
    Qed.

    Theorem intt_fast_closed_form :
      forall n (t : tree int n) i,
        canonical_tree n t ->
        (i < pow2 n)%nat ->
        value (input_get n (intt_fast n t) i) =
        zmul (value (inv_pow2 n))
          (zsum (pow2 n)
            (fun k =>
               zmul (value (output_get n t k))
                 (zpow (value (inv_root n)) ((i * k)%nat)))).
    Proof.
      intros n t i Ht Hi.
      rewrite intt_fast_eq by exact Ht.
      unfold intt, scale_tree.
      rewrite input_get_map_tree by exact Hi.
      rewrite value_mul_mod.
      rewrite intt_raw_correct_dif by assumption.
      rewrite idft_dif_raw_closed_form by assumption.
      reflexivity.
    Qed.
  End InverseFast.

End TreeNTTSpectral.
