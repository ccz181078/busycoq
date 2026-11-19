From Coq Require Import ZArith Lia.
Require Import BigInt.NTTTree BigInt.NTTSpectral BigInt.NTTKernel.

Local Open Scope Z_scope.

Module TreeNTTKernelBounded (C : NTTBaseCfg).
  Module K := TreeNTTKernel(C).
  Module Spect := TreeNTTSpectral(C).
  Module Conv := Spect.Conv.
  Module T := Spect.T.
  Import T Conv Spect K.

  Section KernelBounded.
    Variable max_n : nat.

    Hypothesis root_square_upto :
      forall n,
        (n < max_n)%nat ->
        zpow (value (root (S n))) 2%nat = value (root n).

    Hypothesis root_half_neg_upto :
      forall n,
        (n < max_n)%nat ->
        zpow (value (root (S n))) (pow2 n) = zminus_one.

    Hypothesis inv_root_square_upto :
      forall n,
        (n < max_n)%nat ->
        zpow (value (inv_root (S n))) 2%nat = value (inv_root n).

    Hypothesis inv_root_half_neg_upto :
      forall n,
        (n < max_n)%nat ->
        zpow (value (inv_root (S n))) (pow2 n) = zminus_one.

    Hypothesis inv_root_as_root_pred_upto :
      forall n,
        (n <= max_n)%nat ->
        value (inv_root n) = zpow (value (root n)) (Nat.pred (pow2 n)).

    Hypothesis inv_pow2_zero :
      value (inv_pow2 0%nat) = zone.

    Hypothesis inv_pow2_double_upto :
      forall n,
        (n < max_n)%nat ->
        zadd (value (inv_pow2 (S n))) (value (inv_pow2 (S n))) =
        value (inv_pow2 n).

    Lemma root_even_power_bounded :
      forall n m,
        (n < max_n)%nat ->
        zpow (value (root (S n))) (2 * m)%nat =
        zpow (value (root n)) m.
    Proof.
      intros n m Hn.
      rewrite zpow_mul.
      rewrite root_square_upto by exact Hn.
      reflexivity.
    Qed.

    Lemma root0_one_bounded :
      (0 < max_n)%nat ->
      value (root 0%nat) = zone.
    Proof.
      intro Hmax.
      rewrite <- (root_square_upto 0%nat Hmax).
      replace 2%nat with ((pow2 0%nat) * 2)%nat by reflexivity.
      rewrite zpow_mul.
      rewrite root_half_neg_upto by exact Hmax.
      apply zpow_zminus_one_two.
    Qed.

    Lemma root_period_multiple_bounded :
      forall n q,
        (n < max_n)%nat ->
        zpow (value (root n)) ((pow2 n) * q)%nat = zone.
    Proof.
      intros n q Hn.
      rewrite zpow_mul.
      assert (Hperiod : zpow (value (root n)) (pow2 n) = zone).
      {
        destruct n as [|n].
        - change (pow2 0%nat) with 1%nat.
          rewrite zpow_1.
          rewrite root0_one_bounded by lia.
          apply zcanon_zone.
        - replace (pow2 (S n)) with ((pow2 n) * 2)%nat.
          2:{
            rewrite pow2_succ.
            lia.
          }
          rewrite zpow_mul.
          rewrite root_half_neg_upto by lia.
          apply zpow_zminus_one_two.
      }
      rewrite Hperiod.
      apply zpow_zone.
    Qed.

    Lemma root_period_even_bounded :
      forall n j,
        (n < max_n)%nat ->
        zpow (value (root (S n))) (2 * (j * pow2 n))%nat = zone.
    Proof.
      intros n j Hn.
      replace (2 * (j * pow2 n))%nat with ((pow2 n) * (2 * j))%nat by lia.
      rewrite zpow_mul.
      rewrite root_half_neg_upto by exact Hn.
      apply zpow_zminus_one_even.
    Qed.

    Lemma root_period_odd_bounded :
      forall n j,
        (n < max_n)%nat ->
        zpow (value (root (S n))) ((S (2 * j)) * pow2 n)%nat = zminus_one.
    Proof.
      intros n j Hn.
      replace ((S (2 * j)) * pow2 n)%nat with ((pow2 n) * (S (2 * j)))%nat by lia.
      rewrite zpow_mul.
      rewrite root_half_neg_upto by exact Hn.
      apply zpow_zminus_one_odd.
    Qed.

    Lemma inv_root_even_power_bounded :
      forall n m,
        (n < max_n)%nat ->
        zpow (value (inv_root (S n))) (2 * m)%nat =
        zpow (value (inv_root n)) m.
    Proof.
      intros n m Hn.
      rewrite zpow_mul.
      rewrite inv_root_square_upto by exact Hn.
      reflexivity.
    Qed.

    Lemma inv_root_period_odd_bounded :
      forall n j,
        (n < max_n)%nat ->
        zpow (value (inv_root (S n))) ((S (2 * j)) * pow2 n)%nat = zminus_one.
    Proof.
      intros n j Hn.
      replace ((S (2 * j)) * pow2 n)%nat with ((pow2 n) * (S (2 * j)))%nat by lia.
      rewrite zpow_mul.
      rewrite inv_root_half_neg_upto by exact Hn.
      apply zpow_zminus_one_odd.
    Qed.

    Lemma inv_root_period_even_bounded :
      forall n j,
        (n < max_n)%nat ->
        zpow (value (inv_root (S n))) (2 * (j * pow2 n))%nat = zone.
    Proof.
      intros n j Hn.
      replace (2 * (j * pow2 n))%nat with ((pow2 n) * (2 * j))%nat by lia.
      rewrite zpow_mul.
      rewrite inv_root_half_neg_upto by exact Hn.
      apply zpow_zminus_one_even.
    Qed.

    Lemma zmul_perm4_alt :
      forall a b c d,
        zmul a (zmul b (zmul c d)) =
        zmul d (zmul c (zmul a b)).
    Proof.
      intros a b c d.
      rewrite (zmul_comm c d).
      rewrite (zmul_perm4 a b d c).
      f_equal.
      rewrite <- zmul_assoc.
      rewrite (zmul_comm b a).
      reflexivity.
    Qed.

    Theorem dft_with_closed_form_bounded :
      forall n (t : tree int n) k,
        (n < max_n)%nat ->
        canonical_tree n t ->
        (k < pow2 n)%nat ->
        dft_with root n t k =
        zsum (pow2 n)
          (fun j =>
             zmul (value (input_get n t j))
               (zpow (value (root n)) ((j * k)%nat))).
    Proof.
      induction n as [|n IH]; intros t k Hn Ht Hk.
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
          rewrite K.zsum_add_distr.
          rewrite K.zsum_ext with
            (g := fun j =>
               zmul (value (input_get n l j))
                 (zpow (value (root n)) ((j * k)%nat))).
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
            apply root_even_power_bounded.
            lia.
          }
          transitivity
            (zadd
               (zsum (pow2 n)
                  (fun j =>
                     zmul (value (input_get n l j))
                       (zpow (value (root n)) ((j * k)%nat))))
               (zmul (zpow (value (root (S n))) k)
                  (zsum (pow2 n)
                     (fun j =>
                        zmul (value (input_get n r j))
                          (zpow (value (root n)) ((j * k)%nat)))))).
          {
            assert (Hn' : (n < max_n)%nat) by lia.
            rewrite <- (IH l k Hn' Hl Hlt).
            rewrite <- (IH r k Hn' Hr Hlt).
            reflexivity.
          }
          apply f_equal2.
          * reflexivity.
          * transitivity
              (zsum (pow2 n)
                 (fun j =>
                    zmul (zpow (value (root (S n))) k)
                      (zmul (value (input_get n r j))
                        (zpow (value (root n)) ((j * k)%nat))))).
            {
              apply K.zsum_mul_const_l.
            }
            apply K.zsum_ext.
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
              (zpow (value (root (S n))) (2 * (j * k) + k))
              with
              (zmul (zpow (value (root (S n))) (2 * (j * k)))
                 (zpow (value (root (S n))) k))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * k)))
              with (zpow (value (root n)) (j * k))
              by (symmetry; apply root_even_power_bounded; lia).
            rewrite zmul_assoc.
            rewrite (zmul_comm
                       (zpow (value (root (S n))) k)
                       (value (input_get n r j))).
            rewrite <- zmul_assoc.
            f_equal.
            rewrite (zmul_comm
                       (zpow (value (root (S n))) k)
                       (zpow (value (root n)) (j * k))).
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
          rewrite K.zsum_add_distr.
          rewrite K.zsum_ext with
            (g := fun j =>
               zmul (value (input_get n l j))
                 (zpow (value (root n)) ((j * u)%nat))).
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
              (zpow (value (root (S n))) (2 * (j * u) + 2 * (j * pow2 n)))
              with
              (zmul (zpow (value (root (S n))) (2 * (j * u)))
                 (zpow (value (root (S n))) (2 * (j * pow2 n))))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * u)))
              with (zpow (value (root n)) (j * u))
              by (symmetry; apply root_even_power_bounded; lia).
            replace
              (zpow (value (root (S n))) (2 * (j * pow2 n)))
              with zone
              by (symmetry; apply root_period_even_bounded; lia).
            rewrite Conv.zmul_1_r.
            rewrite zpow_canon.
            reflexivity.
          }
          replace
            (zsum (pow2 n)
               (fun j =>
                  zmul (value (input_get (S n) (l, r) (S (2 * j))%nat))
                    (zpow (value (root (S n))) ((S (2 * j) * (u + pow2 n))%nat))))
            with
            (zsum (pow2 n)
               (fun j =>
                  zmul zminus_one
                    (zmul (zpow (value (root (S n))) u)
                      (zmul (value (input_get n r j))
                        (zpow (value (root n)) ((j * u)%nat)))))).
          2:{
            apply K.zsum_ext.
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
              (zpow (value (root (S n)))
                 ((2 * (j * u) + u) + (S (2 * j) * pow2 n)))
              with
              (zmul
                 (zpow (value (root (S n))) (2 * (j * u) + u))
                 (zpow (value (root (S n))) (S (2 * j) * pow2 n)))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * u) + u))
              with
              (zmul (zpow (value (root (S n))) (2 * (j * u)))
                 (zpow (value (root (S n))) u))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * u)))
              with (zpow (value (root n)) (j * u))
              by (symmetry; apply root_even_power_bounded; lia).
            replace
              (zpow (value (root (S n))) (S (2 * j) * pow2 n))
              with zminus_one
              by (symmetry; apply root_period_odd_bounded; lia).
            apply zmul_perm4.
          }
          transitivity
            (zadd
               (zsum (pow2 n)
                  (fun j =>
                     zmul (value (input_get n l j))
                       (zpow (value (root n)) ((j * u)%nat))))
               (zsum (pow2 n)
                  (fun j =>
                     zmul zminus_one
                       (zmul (zpow (value (root (S n))) u)
                         (zmul (value (input_get n r j))
                           (zpow (value (root n)) ((j * u)%nat))))))).
          {
            assert (Hn' : (n < max_n)%nat) by lia.
            rewrite <- (IH l u Hn' Hl Hu).
            rewrite <- K.zsum_mul_const_l.
            rewrite <- K.zsum_mul_const_l.
            replace
              (zsum (pow2 n)
                 (fun j =>
                    zmul (value (input_get n r j))
                      (zpow (value (root n)) ((j * u)%nat))))
              with (dft_with root n r u).
            2:{
              apply (IH r u Hn' Hr Hu).
            }
            rewrite zsub_eq_add_neg.
            apply f_equal2.
            - reflexivity.
            - rewrite (zmul_comm
                         (zmul (zpow (value (root (S n))) u) (dft_with root n r u))
                         zminus_one).
              apply f_equal2.
              + reflexivity.
              + apply f_equal2.
                * reflexivity.
                * exact (IH r u Hn' Hr Hu).
          }
          apply f_equal2; [reflexivity|].
          symmetry.
          apply K.zsum_ext.
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
              (zpow (value (root (S n)))
                 ((2 * (j * u) + u) + (S (2 * j) * pow2 n)))
              with
              (zmul
                 (zpow (value (root (S n))) (2 * (j * u) + u))
                 (zpow (value (root (S n))) (S (2 * j) * pow2 n)))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * u) + u))
              with
              (zmul (zpow (value (root (S n))) (2 * (j * u)))
                 (zpow (value (root (S n))) u))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (2 * (j * u)))
              with (zpow (value (root n)) (j * u))
              by (symmetry; apply root_even_power_bounded; lia).
            replace
              (zpow (value (root (S n))) (S (2 * j) * pow2 n))
              with zminus_one
              by (symmetry; apply root_period_odd_bounded; lia).
            repeat rewrite <- zmul_assoc.
            apply zmul_perm4_alt.
    Qed.

    Theorem ntt_fast_closed_form_bounded :
      forall n (t : tree int n) k,
        (n < max_n)%nat ->
        canonical_tree n t ->
        (k < pow2 n)%nat ->
        value (output_get n (ntt_fast n t) k) =
        zsum (pow2 n)
          (fun j =>
             zmul (value (input_get n t j))
               (zpow (value (root n)) ((j * k)%nat))).
    Proof.
      intros n t k Hn Ht Hk.
      rewrite ntt_fast_correct by assumption.
      rewrite <- dft_with_root_eq.
      apply dft_with_closed_form_bounded; assumption.
    Qed.

    Theorem idft_dif_raw_closed_form_bounded :
      forall n (t : tree int n) i,
        (n < max_n)%nat ->
        canonical_tree n t ->
        (i < pow2 n)%nat ->
        idft_dif_raw n t i =
        zsum (pow2 n)
          (fun k =>
             zmul (value (output_get n t k))
               (zpow (value (inv_root n)) ((i * k)%nat))).
    Proof.
      induction n as [|n IH]; intros t i Hn Ht Hi.
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
          assert (Hn' : (n < max_n)%nat) by lia.
          rewrite (IH (zip_tree n add_mod l r) j Hn').
          2:{ apply canonical_zip_add; assumption. }
          2:{ exact Hj. }
          subst j.
          rewrite K.zsum_ext with
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
          rewrite K.zsum_add_distr.
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
          * apply K.zsum_ext.
            intros k Hk.
            rewrite output_get_left by exact Hk.
            replace ((2 * Nat.div2 i * k)%nat) with (2 * (Nat.div2 i * k))%nat by lia.
            rewrite inv_root_even_power_bounded by exact Hn'.
            reflexivity.
          * apply K.zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            rewrite output_get_right by exact Hk.
            replace ((2 * Nat.div2 i) * (k + pow2 n))%nat
              with (2 * (Nat.div2 i * k) + 2 * (Nat.div2 i * pow2 n))%nat by lia.
            rewrite (zpow_add (value (inv_root (S n)))
                        (2 * (Nat.div2 i * k)) (2 * (Nat.div2 i * pow2 n))).
            rewrite inv_root_even_power_bounded by exact Hn'.
            rewrite inv_root_period_even_bounded by exact Hn'.
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
          assert (Hn' : (n < max_n)%nat) by lia.
          rewrite (IH (twiddle_tree n (inv_root (S n)) (zip_tree n sub_mod l r)) j Hn').
          2:{
            apply canonical_twiddle_from.
            apply canonical_zip_sub; assumption.
          }
          2:{ exact Hj. }
          subst j.
          rewrite K.zsum_ext with
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
          rewrite K.zsum_ext with
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
          rewrite K.zsum_ext with
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
          rewrite K.zsum_add_distr.
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
          * apply K.zsum_ext.
            intros k Hk.
            rewrite output_get_left by exact Hk.
            replace ((S (2 * Nat.div2 i) * k)%nat)
              with ((k + 2 * (Nat.div2 i * k))%nat) by lia.
            rewrite zpow_add.
            rewrite inv_root_even_power_bounded by exact Hn'.
            rewrite zmul_assoc.
            reflexivity.
          * apply K.zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            rewrite output_get_right by exact Hk.
            replace ((S (2 * Nat.div2 i)) * (k + pow2 n))%nat
              with ((k + 2 * (Nat.div2 i * k)) + (S (2 * Nat.div2 i) * pow2 n))%nat by lia.
            rewrite zpow_add.
            rewrite zpow_add.
            rewrite inv_root_even_power_bounded by exact Hn'.
            rewrite inv_root_period_odd_bounded by exact Hn'.
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

    Theorem intt_fast_closed_form_bounded :
      forall n (t : tree int n) i,
        (n < max_n)%nat ->
        canonical_tree n t ->
        (i < pow2 n)%nat ->
        value (input_get n (intt_fast n t) i) =
        zmul (value (inv_pow2 n))
          (zsum (pow2 n)
            (fun k =>
               zmul (value (output_get n t k))
                 (zpow (value (inv_root n)) ((i * k)%nat)))).
    Proof.
      intros n t i Hn Ht Hi.
      rewrite intt_fast_eq by exact Ht.
      unfold intt, idft_dif, scale_tree.
      rewrite input_get_map_tree by exact Hi.
      rewrite value_mul_mod.
      rewrite intt_raw_correct_dif by assumption.
      rewrite idft_dif_raw_closed_form_bounded by assumption.
      reflexivity.
    Qed.

    Theorem scaled_root_sum_small_bounded :
      forall n m,
        (n < max_n)%nat ->
        (m < pow2 n)%nat ->
        zmul (value (inv_pow2 n))
          (zsum (pow2 n)
            (fun k => zpow (value (root n)) ((m * k)%nat))) =
        delta_nat 0%nat m.
    Proof.
      induction n as [|n IH]; intros m Hn Hm.
      - change (pow2 0%nat) with 1%nat in Hm.
        assert (Hm0 : m = 0%nat) by lia.
        subst m.
        change (pow2 0%nat) with 1%nat.
        rewrite inv_pow2_zero.
        rewrite zmul_1_l.
        replace (zsum 1%nat (fun k => zpow (value (root 0%nat)) ((0 * k)%nat)))
          with zone.
        2:{
          cbn [zsum zpow].
          rewrite zadd_0_l.
          symmetry.
          apply zcanon_zone.
        }
        unfold delta_nat.
        rewrite Nat.eqb_refl.
        apply zcanon_zone.
      - destruct (Nat.even m) eqn:Hev.
        + set (j := Nat.div2 m).
          assert (Heq : (m = 2 * j)%nat).
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
            rewrite pow2_succ in Hm.
            rewrite Heq in Hm.
            lia.
          }
          assert (Hn' : (n < max_n)%nat) by lia.
          subst j.
          rewrite Heq.
          replace (pow2 (S n)) with ((pow2 n + pow2 n)%nat) by (symmetry; apply pow2_succ).
          replace
            (zsum (pow2 n + pow2 n)
               (fun k =>
                  zpow (value (root (S n))) ((2 * Nat.div2 m * k)%nat)))
            with
              (zadd
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n))) ((2 * Nat.div2 m * k)%nat)))
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n)))
                        ((2 * Nat.div2 m * (k + pow2 n))%nat)))).
          2:{
            symmetry.
            apply zsum_split_at.
          }
          replace
            (zsum (pow2 n)
               (fun k =>
                  zpow (value (root (S n))) ((2 * Nat.div2 m * k)%nat)))
            with
              (zsum (pow2 n)
                 (fun k =>
                    zpow (value (root n)) ((Nat.div2 m * k)%nat))).
          2:{
            apply K.zsum_ext.
            intros k Hk.
            replace ((2 * Nat.div2 m * k)%nat)
              with (2 * (Nat.div2 m * k))%nat by lia.
            rewrite root_even_power_bounded by exact Hn'.
            reflexivity.
          }
          replace
            (zsum (pow2 n)
               (fun k =>
                  zpow (value (root (S n)))
                    ((2 * Nat.div2 m * (k + pow2 n))%nat)))
            with
              (zsum (pow2 n)
                 (fun k =>
                    zpow (value (root n)) ((Nat.div2 m * k)%nat))).
          2:{
            apply K.zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            replace ((2 * Nat.div2 m * (k + pow2 n))%nat)
              with (2 * (Nat.div2 m * k) + 2 * (Nat.div2 m * pow2 n))%nat by lia.
            rewrite zpow_add.
            rewrite root_even_power_bounded by exact Hn'.
            rewrite root_period_even_bounded by exact Hn'.
            rewrite zmul_1_r.
            symmetry.
            apply zpow_canon.
          }
          rewrite zmul_add_distr_l.
          rewrite <- zmul_add_distr_r.
          rewrite inv_pow2_double_upto by exact Hn'.
          rewrite IH by assumption.
          destruct (Nat.div2 m); reflexivity.
        + set (j := Nat.div2 m).
          assert (Heq : (m = S (2 * j))%nat).
          {
            subst j.
            assert (Hodd : Nat.odd m = true).
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
          assert (Hn' : (n < max_n)%nat) by lia.
          subst j.
          rewrite Heq.
          replace (pow2 (S n)) with ((pow2 n + pow2 n)%nat) by (symmetry; apply pow2_succ).
          replace
            (zsum (pow2 n + pow2 n)
               (fun k =>
                  zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat)))
            with
              (zadd
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat)))
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n)))
                        ((S (2 * Nat.div2 m) * (k + pow2 n))%nat)))).
          2:{
            symmetry.
            apply zsum_split_at.
          }
          replace
            (zsum (pow2 n)
               (fun k =>
                  zpow (value (root (S n)))
                    ((S (2 * Nat.div2 m) * (k + pow2 n))%nat)))
            with
              (zsum (pow2 n)
                 (fun k =>
                    zmul
                      (zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat))
                      zminus_one)).
          2:{
            apply K.zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            replace ((S (2 * Nat.div2 m) * (k + pow2 n))%nat)
              with ((S (2 * Nat.div2 m) * k + S (2 * Nat.div2 m) * pow2 n)%nat) by lia.
            replace
              (zpow (value (root (S n))) (S (2 * Nat.div2 m) * k + S (2 * Nat.div2 m) * pow2 n))
              with
                (zmul
                   (zpow (value (root (S n))) (S (2 * Nat.div2 m) * k))
                   (zpow (value (root (S n))) (S (2 * Nat.div2 m) * pow2 n)))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (S (2 * Nat.div2 m) * pow2 n))
              with zminus_one.
            2:{
              symmetry.
              apply root_period_odd_bounded.
              exact Hn'.
            }
            reflexivity.
          }
          replace
            (zsum (pow2 n)
               (fun k =>
                  zmul
                    (zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat))
                    zminus_one))
            with
              (zmul
                 (zsum (pow2 n)
                    (fun k =>
                       zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat)))
                 zminus_one).
          2:{
            apply K.zsum_mul_const_r.
          }
          set (s :=
            zsum (pow2 n)
              (fun k =>
                 zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat))).
          replace
            (zsum (pow2 n)
               (fun k =>
                  zpow (value (root (S n))) ((S (2 * Nat.div2 m) * k)%nat)))
            with s by reflexivity.
          rewrite zmul_add_distr_l.
          rewrite zmul_assoc.
          rewrite zadd_opp_r.
          unfold delta_nat.
          reflexivity.
    Qed.

    Theorem convolution_kernel_bounded :
      forall n i j l,
        (n < max_n)%nat ->
        (i < pow2 n)%nat ->
        (j < pow2 n)%nat ->
        (l < pow2 n)%nat ->
        zmul (value (inv_pow2 n))
          (zsum (pow2 n)
            (fun k =>
               zmul (zpow (value (root n)) ((j * k)%nat))
                 (zmul (zpow (value (root n)) ((l * k)%nat))
                   (zpow (value (inv_root n)) ((i * k)%nat))))) =
        delta_nat i ((j + l) mod pow2 n)%nat.
    Proof.
      intros n i j l Hn Hi Hj Hl.
      set (len := pow2 n).
      set (h := ((j + l) mod len)%nat).
      set (q := ((j + l) / len)%nat).
      assert (Hlen : (0 < len)%nat).
      {
        subst len.
        apply pow2_pos.
      }
      assert (Hsum : (j + l = len * q + h)%nat).
      {
        subst h q.
        apply Nat.div_mod.
        pose proof Hlen.
        lia.
      }
      assert (Hh : (h < len)%nat).
      {
        subst h.
        apply Nat.mod_upper_bound.
        pose proof Hlen.
        lia.
      }
      destruct (Nat.leb_spec0 i h) as [Hle|Hgt].
      - rewrite K.zsum_ext with
          (g := fun k =>
             zpow (value (root n)) (((h - i) * k)%nat)).
        2:{
          intros k Hk.
          assert (Hpoint :
            zmul (zpow (value (root n)) ((j * k)%nat))
              (zmul (zpow (value (root n)) ((l * k)%nat))
                (zpow (value (inv_root n)) ((i * k)%nat))) =
            zpow (value (root n)) (((h - i) * k)%nat)).
          {
            rewrite inv_root_as_root_pred_upto by lia.
            rewrite <- zpow_mul.
            replace (Nat.pred (pow2 n)) with (len - 1)%nat by (subst len; lia).
            transitivity
              (zpow (value (root n))
                 ((j * k + (l * k + (len - 1) * (i * k)))%nat)).
            {
              rewrite <- zpow_add.
              rewrite <- zpow_add.
              reflexivity.
            }
            assert (Hex :
              (j * k + (l * k + (len - 1) * (i * k)))%nat =
              (((h - i) * k) + len * ((q + i) * k))%nat).
            {
              replace (j * k + (l * k + (len - 1) * (i * k)))%nat
                with (((j + l) * k + (len - 1) * (i * k))%nat) by nia.
              replace (((j + l) * k + (len - 1) * (i * k))%nat)
                with ((((j + l) + (len - 1) * i) * k)%nat) by nia.
              replace ((((h - i) * k) + len * ((q + i) * k))%nat)
                with ((((h - i) + len * (q + i)) * k)%nat) by nia.
              rewrite Hsum.
              f_equal.
              nia.
            }
            transitivity
              (zpow (value (root n))
                 ((((h - i) * k) + len * ((q + i) * k))%nat)).
            {
              apply f_equal.
              exact Hex.
            }
            transitivity
              (zmul
                 (zpow (value (root n)) (((h - i) * k)%nat))
                 (zpow (value (root n)) (len * ((q + i) * k)))).
            {
              apply zpow_add.
            }
            transitivity
              (zmul
                 (zpow (value (root n)) (((h - i) * k)%nat))
                 zone).
            {
              apply f_equal.
              subst len.
              apply root_period_multiple_bounded.
              exact Hn.
            }
            rewrite zmul_1_r.
            apply zpow_canon.
          }
          exact Hpoint.
        }
        rewrite scaled_root_sum_small_bounded by lia.
        unfold delta_nat.
        destruct (Nat.eq_dec i h) as [Heq|Hneq].
        + rewrite Heq.
          replace (h - h)%nat with 0%nat by lia.
          repeat rewrite Nat.eqb_refl.
          reflexivity.
        + assert (Hneq_left : (0 =? h - i)%nat = false).
          {
            apply Nat.eqb_neq.
            lia.
          }
          assert (Hneq_right : (i =? h)%nat = false).
          {
            apply Nat.eqb_neq.
            lia.
          }
          rewrite Hneq_left.
          rewrite Hneq_right.
          reflexivity.
      - rewrite K.zsum_ext with
          (g := fun k =>
             zpow (value (root n)) (((h + len - i) * k)%nat)).
        2:{
          intros k Hk.
          assert (Hpoint :
            zmul (zpow (value (root n)) ((j * k)%nat))
              (zmul (zpow (value (root n)) ((l * k)%nat))
                (zpow (value (inv_root n)) ((i * k)%nat))) =
            zpow (value (root n)) (((h + len - i) * k)%nat)).
          {
            rewrite inv_root_as_root_pred_upto by lia.
            rewrite <- zpow_mul.
            replace (Nat.pred (pow2 n)) with (len - 1)%nat by (subst len; lia).
            transitivity
              (zpow (value (root n))
                 ((j * k + (l * k + (len - 1) * (i * k)))%nat)).
            {
              rewrite <- zpow_add.
              rewrite <- zpow_add.
              reflexivity.
            }
            assert (Hi_pos : (0 < i)%nat) by lia.
            assert (Hex :
              (j * k + (l * k + (len - 1) * (i * k)))%nat =
              (((h + len - i) * k) + len * ((q + i - 1) * k))%nat).
            {
              replace (j * k + (l * k + (len - 1) * (i * k)))%nat
                with (((j + l) * k + (len - 1) * (i * k))%nat) by nia.
              replace (((j + l) * k + (len - 1) * (i * k))%nat)
                with ((((j + l) + (len - 1) * i) * k)%nat) by nia.
              replace ((((h + len - i) * k) + len * ((q + i - 1) * k))%nat)
                with ((((h + len - i) + len * (q + i - 1)) * k)%nat) by nia.
              rewrite Hsum.
              f_equal.
              nia.
            }
            transitivity
              (zpow (value (root n))
                 ((((h + len - i) * k) + len * ((q + i - 1) * k))%nat)).
            {
              apply f_equal.
              exact Hex.
            }
            transitivity
              (zmul
                 (zpow (value (root n)) (((h + len - i) * k)%nat))
                 (zpow (value (root n)) (len * ((q + i - 1) * k)))).
            {
              apply zpow_add.
            }
            transitivity
              (zmul
                 (zpow (value (root n)) (((h + len - i) * k)%nat))
                 zone).
            {
              apply f_equal.
              subst len.
              apply root_period_multiple_bounded.
              exact Hn.
            }
            rewrite zmul_1_r.
            apply zpow_canon.
          }
          exact Hpoint.
        }
        rewrite scaled_root_sum_small_bounded by lia.
        unfold delta_nat.
        assert (Hneq_left : (0 =? h + len - i)%nat = false).
        {
          apply Nat.eqb_neq.
          lia.
        }
        assert (Hneq_right : (i =? h)%nat = false).
        {
          apply Nat.eqb_neq.
          lia.
        }
        rewrite Hneq_left.
        rewrite Hneq_right.
        reflexivity.
    Qed.

    Theorem intt_fast_pointwise_mul_ntt_fast_cyclic_convolution_bounded :
      forall n (a b : tree int n) i,
        (n < max_n)%nat ->
        canonical_tree n a ->
        canonical_tree n b ->
        (i < pow2 n)%nat ->
        value
          (input_get n
            (intt_fast n
              (zip_tree n mul_mod (ntt_fast n a) (ntt_fast n b))) i) =
        cyclic_convolution n a b i.
    Proof.
      intros n a b i Hn Ha Hb Hi.
      set (freq := zip_tree n mul_mod (ntt_fast n a) (ntt_fast n b)).
      assert (Hfa : canonical_tree n (ntt_fast n a)).
      {
        rewrite ntt_fast_eq by exact Ha.
        apply canonical_ntt.
        exact Ha.
      }
      assert (Hfb : canonical_tree n (ntt_fast n b)).
      {
        rewrite ntt_fast_eq by exact Hb.
        apply canonical_ntt.
        exact Hb.
      }
      assert (Hfreq : canonical_tree n freq).
      {
        subst freq.
        apply K.canonical_zip_mul_local; assumption.
      }
      change
        (value (input_get n (intt_fast n freq) i) =
         cyclic_convolution n a b i).
      rewrite (intt_fast_closed_form_bounded n freq i Hn Hfreq Hi).
      subst freq.
      unfold cyclic_convolution.
      rewrite K.zsum_ext with
        (g := fun k =>
           zmul
             (zmul (value (output_get n (ntt_fast n a) k))
               (value (output_get n (ntt_fast n b) k)))
             (zpow (value (inv_root n)) ((i * k)%nat))).
      2:{
        intros k Hk.
        rewrite output_get_zip_tree by exact Hk.
        rewrite value_mul_mod.
        reflexivity.
      }
      rewrite K.zsum_ext with
        (g := fun k =>
           zmul
             (zsum (pow2 n)
               (fun j =>
                  zmul (value (input_get n a j))
                    (zpow (value (root n)) ((j * k)%nat))))
             (zmul
               (zsum (pow2 n)
                 (fun l =>
                    zmul (value (input_get n b l))
                      (zpow (value (root n)) ((l * k)%nat))))
               (zpow (value (inv_root n)) ((i * k)%nat)))).
      2:{
        intros k Hk.
        rewrite (ntt_fast_closed_form_bounded n a k Hn Ha Hk).
        rewrite (ntt_fast_closed_form_bounded n b k Hn Hb Hk).
        rewrite zmul_assoc.
        reflexivity.
      }
      rewrite K.zsum_ext with
        (g := fun k =>
           zsum (pow2 n)
             (fun j =>
                zsum (pow2 n)
                  (fun l =>
                     zmul (zmul (value (input_get n a j))
                             (zpow (value (root n)) ((j * k)%nat)))
                       (zmul (zmul (value (input_get n b l))
                               (zpow (value (root n)) ((l * k)%nat)))
                         (zpow (value (inv_root n)) ((i * k)%nat)))))).
      2:{
        intros k Hk.
        set (sa :=
          zsum (pow2 n)
            (fun j =>
               zmul (value (input_get n a j))
                 (zpow (value (root n)) ((j * k)%nat)))).
        rewrite K.zsum_mul_const_r.
        subst sa.
        rewrite K.zsum_mul_expand.
        reflexivity.
      }
      rewrite K.zsum_swap.
      rewrite K.zsum_ext with
        (g := fun j =>
           zsum (pow2 n)
             (fun l =>
                zsum (pow2 n)
                  (fun k =>
                     zmul (value (input_get n a j))
                       (zmul (value (input_get n b l))
                         (zmul (zpow (value (root n)) ((j * k)%nat))
                           (zmul (zpow (value (root n)) ((l * k)%nat))
                             (zpow (value (inv_root n)) ((i * k)%nat)))))))).
      2:{
        intros j Hj.
        rewrite K.zsum_swap.
        apply K.zsum_ext.
        intros l Hl.
        apply K.zsum_ext.
        intros k Hk.
        repeat rewrite <- zmul_assoc.
        f_equal.
        rewrite zmul_assoc.
        rewrite (zmul_comm (zpow (value (root n)) ((j * k)%nat))
                  (value (input_get n b l))).
        repeat rewrite <- zmul_assoc.
        reflexivity.
      }
      rewrite K.zsum_mul_const_l.
      apply K.zsum_ext.
      intros j Hj.
      rewrite K.zsum_mul_const_l.
      apply K.zsum_ext.
      intros l Hl.
      rewrite <- K.zsum_mul_const_l.
      rewrite <- K.zsum_mul_const_l.
      rewrite zmul_assoc.
      rewrite (zmul_comm (value (inv_pow2 n))
                (value (input_get n a j))).
      repeat rewrite <- zmul_assoc.
      f_equal.
      rewrite zmul_assoc.
      rewrite (zmul_comm (value (inv_pow2 n))
                (value (input_get n b l))).
      repeat rewrite <- zmul_assoc.
      f_equal.
      exact (convolution_kernel_bounded n i j l Hn Hi Hj Hl).
    Qed.
  End KernelBounded.
End TreeNTTKernelBounded.
