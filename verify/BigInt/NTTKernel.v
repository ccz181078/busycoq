From Coq Require Import ZArith Lia.
Require Import BigInt.NTTTree BigInt.NTTSpectral.

Local Open Scope Z_scope.

Module TreeNTTKernel (C : NTTBaseCfg).
  Module Spect := TreeNTTSpectral(C).
  Module T := Spect.T.
  Import T Spect.

  Section Kernel.
    Hypothesis root_square :
      forall n,
        zpow (value (root (S n))) 2%nat = value (root n).

    Hypothesis root_half_neg :
      forall n,
        zpow (value (root (S n))) (pow2 n) = zminus_one.

    Hypothesis inv_root_square :
      forall n,
        zpow (value (inv_root (S n))) 2%nat = value (inv_root n).

    Hypothesis inv_root_half_neg :
      forall n,
        zpow (value (inv_root (S n))) (pow2 n) = zminus_one.

    Hypothesis inv_root_as_root_pred :
      forall n,
        value (inv_root n) = zpow (value (root n)) (Nat.pred (pow2 n)).

    Hypothesis inv_pow2_zero :
      value (inv_pow2 0%nat) = zone.

    Hypothesis inv_pow2_double :
      forall n,
        zadd (value (inv_pow2 (S n))) (value (inv_pow2 (S n))) =
        value (inv_pow2 n).

    Definition delta_nat (i j : nat) : Z :=
      if Nat.eqb i j then zone else zzero.

    Lemma root_even_power :
      forall n m,
        zpow (value (root (S n))) (2 * m)%nat =
        zpow (value (root n)) m.
    Proof.
      intros n m.
      rewrite zpow_mul.
      rewrite root_square.
      reflexivity.
    Qed.

    Lemma root0_one :
      value (root 0%nat) = zone.
    Proof.
      rewrite <- (root_square 0%nat).
      replace 2%nat with ((pow2 0%nat) * 2)%nat by reflexivity.
      rewrite zpow_mul.
      rewrite root_half_neg.
      apply zpow_zminus_one_two.
    Qed.

    Lemma root_period :
      forall n,
        zpow (value (root n)) (pow2 n) = zone.
    Proof.
      intros [|n].
      - change (pow2 0%nat) with 1%nat.
        rewrite zpow_1.
        rewrite root0_one.
        apply zcanon_zone.
      - replace (pow2 (S n)) with ((pow2 n) * 2)%nat.
        2:{
          rewrite pow2_succ.
          lia.
        }
        rewrite zpow_mul.
        rewrite root_half_neg.
        apply zpow_zminus_one_two.
    Qed.

    Lemma root_period_multiple :
      forall n q,
        zpow (value (root n)) ((pow2 n) * q)%nat = zone.
    Proof.
      intros n q.
      rewrite zpow_mul.
      rewrite root_period.
      apply zpow_zone.
    Qed.

    Lemma root_period_even :
      forall n j,
        zpow (value (root (S n))) (2 * (j * pow2 n))%nat = zone.
    Proof.
      intros n j.
      replace (2 * (j * pow2 n))%nat with ((pow2 n) * (2 * j))%nat by lia.
      rewrite zpow_mul.
      rewrite root_half_neg.
      apply zpow_zminus_one_even.
    Qed.

    Lemma root_period_odd :
      forall n j,
        zpow (value (root (S n))) ((S (2 * j)) * pow2 n)%nat = zminus_one.
    Proof.
      intros n j.
      replace ((S (2 * j)) * pow2 n)%nat with ((pow2 n) * (S (2 * j)))%nat by lia.
      rewrite zpow_mul.
      rewrite root_half_neg.
        apply zpow_zminus_one_odd.
    Qed.

    Lemma zcanon_0 : zcanon 0 = 0.
    Proof.
      unfold zcanon.
      apply Z.mod_small.
      split.
      - lia.
      - exact modulus_pos.
    Qed.

    Lemma zmul_1_r : forall x, zmul x zone = zcanon x.
    Proof.
      intro x.
      rewrite zmul_comm.
      apply zmul_1_l.
    Qed.

    Lemma zadd_0_r : forall x, zadd x zzero = zcanon x.
    Proof.
      intro x.
      rewrite zadd_comm.
      apply zadd_0_l.
    Qed.

    Lemma zsum_ext :
      forall n (f g : nat -> Z),
        (forall i, (i < n)%nat -> f i = g i) ->
        zsum n f = zsum n g.
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

    Lemma zmul_0_l : forall x, zmul zzero x = zzero.
    Proof.
      intro x.
      unfold zmul, zzero.
      rewrite Z.mul_0_l.
      apply zcanon_0.
    Qed.

    Lemma zmul_0_r : forall x, zmul x zzero = zzero.
    Proof.
      intro x.
      rewrite zmul_comm.
      apply zmul_0_l.
    Qed.

    Lemma zsum_zero :
      forall n, zsum n (fun _ => zzero) = zzero.
    Proof.
      induction n as [|n IH].
      - reflexivity.
      - simpl.
        rewrite IH.
        apply zadd_0_r.
    Qed.

    Lemma zmul_add_distr_l : forall x y z,
        zmul x (zadd y z) = zadd (zmul x y) (zmul x z).
    Proof.
      intros x y z.
      unfold zadd, zmul.
      rewrite zcanon_mul_idemp_r.
      rewrite zcanon_add.
      rewrite Z.mul_add_distr_l.
      reflexivity.
    Qed.

    Lemma zsum_add_distr :
      forall n (f g : nat -> Z),
        zsum n (fun i => zadd (f i) (g i)) = zadd (zsum n f) (zsum n g).
    Proof.
      induction n as [|n IH]; intros f g.
      - simpl.
        rewrite zadd_0_l.
        symmetry.
        apply zcanon_0.
      - simpl.
        rewrite IH.
        set (a0 := zsum n f).
        set (b0 := zsum n g).
        set (c0 := f n).
        set (d0 := g n).
        change (zadd (zadd a0 b0) (zadd c0 d0) =
                zadd (zadd a0 c0) (zadd b0 d0)).
        transitivity (zadd a0 (zadd b0 (zadd c0 d0))).
        + rewrite <- zadd_assoc.
          reflexivity.
        + transitivity (zadd a0 (zadd c0 (zadd b0 d0))).
          * f_equal.
            rewrite zadd_assoc.
            rewrite (zadd_comm b0 c0).
            rewrite <- zadd_assoc.
            reflexivity.
          * rewrite zadd_assoc.
            reflexivity.
    Qed.

    Lemma zsum_mul_const_l :
      forall n c (f : nat -> Z),
        zmul c (zsum n f) = zsum n (fun i => zmul c (f i)).
    Proof.
      induction n as [|n IH]; intros c f.
      - simpl.
        apply zmul_0_r.
      - simpl.
        rewrite zmul_add_distr_l.
        rewrite IH.
        reflexivity.
    Qed.

    Lemma zsum_mul_const_r :
      forall n c (f : nat -> Z),
        zmul (zsum n f) c = zsum n (fun i => zmul (f i) c).
    Proof.
      intros n c f.
      rewrite zmul_comm.
      rewrite zsum_mul_const_l.
      apply zsum_ext.
      intros i Hi.
      apply zmul_comm.
    Qed.

    Lemma zsum_swap :
      forall n m (f : nat -> nat -> Z),
        zsum n (fun i => zsum m (fun j => f i j)) =
        zsum m (fun j => zsum n (fun i => f i j)).
    Proof.
      induction n as [|n IH]; intros m f.
      - simpl.
        symmetry.
        apply zsum_zero.
      - simpl.
        rewrite IH.
        rewrite <- zsum_add_distr.
        apply zsum_ext.
        intros j Hj.
        simpl.
        rewrite zadd_comm.
        reflexivity.
    Qed.

    Lemma zsum_mul_expand :
      forall n m (f : nat -> Z) (g : nat -> Z),
        zmul (zsum n f) (zsum m g) =
        zsum n (fun i => zsum m (fun j => zmul (f i) (g j))).
    Proof.
      induction n as [|n IH]; intros m f g.
      - simpl.
        apply zmul_0_l.
      - simpl.
        rewrite zmul_add_distr_r.
        rewrite IH.
        rewrite zsum_mul_const_l.
        reflexivity.
    Qed.

    Lemma zadd_opp_r :
      forall x,
        zadd x (zmul x zminus_one) = zzero.
    Proof.
      intro x.
      rewrite <- zsub_eq_add_neg.
      unfold T.zsub, T.zzero.
      replace (x - x)%Z with 0%Z by lia.
      apply zcanon_0.
    Qed.

    Theorem scaled_root_sum_small :
      forall n m,
        (m < pow2 n)%nat ->
        zmul (value (inv_pow2 n))
          (zsum (pow2 n)
            (fun k => zpow (value (root n)) ((m * k)%nat))) =
        delta_nat 0%nat m.
    Proof.
      induction n as [|n IH]; intros m Hm.
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
            apply zsum_ext.
            intros k Hk.
            replace ((2 * Nat.div2 m * k)%nat)
              with (2 * (Nat.div2 m * k))%nat by lia.
            rewrite root_even_power.
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
            apply zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            replace ((2 * Nat.div2 m * (k + pow2 n))%nat)
              with (2 * (Nat.div2 m * k) + 2 * (Nat.div2 m * pow2 n))%nat by lia.
            rewrite zpow_add.
            rewrite root_even_power.
            rewrite root_period_even.
            rewrite zmul_1_r.
            symmetry.
            apply zpow_canon.
          }
          rewrite zmul_add_distr_l.
          rewrite <- zmul_add_distr_r.
          rewrite inv_pow2_double.
          rewrite IH by exact Hj.
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
          rewrite Heq.
          replace (pow2 (S n)) with ((pow2 n + pow2 n)%nat) by (symmetry; apply pow2_succ).
          replace
            (zsum (pow2 n + pow2 n)
               (fun k =>
                  zpow (value (root (S n))) ((S (2 * j) * k)%nat)))
            with
              (zadd
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n))) ((S (2 * j) * k)%nat)))
                 (zsum (pow2 n)
                   (fun k =>
                      zpow (value (root (S n)))
                        ((S (2 * j) * (k + pow2 n))%nat)))).
          2:{
            symmetry.
            apply zsum_split_at.
          }
          replace
            (zsum (pow2 n)
               (fun k =>
                  zpow (value (root (S n)))
                    ((S (2 * j) * (k + pow2 n))%nat)))
            with
              (zsum (pow2 n)
                 (fun k =>
                    zmul
                      (zpow (value (root (S n))) ((S (2 * j) * k)%nat))
                      zminus_one)).
          2:{
            apply zsum_ext.
            intros k Hk.
            replace ((k + pow2 n)%nat) with (Nat.add k (pow2 n)) by lia.
            replace ((S (2 * j) * (k + pow2 n))%nat)
              with ((S (2 * j) * k + S (2 * j) * pow2 n)%nat) by lia.
            replace
              (zpow (value (root (S n))) (S (2 * j) * k + S (2 * j) * pow2 n))
              with
                (zmul
                   (zpow (value (root (S n))) (S (2 * j) * k))
                   (zpow (value (root (S n))) (S (2 * j) * pow2 n)))
              by (symmetry; apply zpow_add).
            replace
              (zpow (value (root (S n))) (S (2 * j) * pow2 n))
              with zminus_one.
            2:{
              symmetry.
              apply root_period_odd.
            }
            reflexivity.
          }
          rewrite <- zsum_mul_const_r.
          rewrite zadd_opp_r.
          rewrite zmul_0_r.
          unfold delta_nat.
          reflexivity.
    Qed.

    Theorem convolution_kernel :
      forall n i j l,
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
      intros n i j l Hi Hj Hl.
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
      - rewrite zsum_ext with
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
            rewrite inv_root_as_root_pred.
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
              apply root_period_multiple.
            }
            rewrite zmul_1_r.
            apply zpow_canon.
          }
          exact Hpoint.
        }
        rewrite scaled_root_sum_small by lia.
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
      - rewrite zsum_ext with
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
            rewrite inv_root_as_root_pred.
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
              apply root_period_multiple.
            }
            rewrite zmul_1_r.
            apply zpow_canon.
          }
          exact Hpoint.
        }
        rewrite scaled_root_sum_small by lia.
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

    Definition cyclic_convolution_local (n : nat) (a b : tree int n) (i : nat) : Z :=
      let len := pow2 n in
      zsum len
        (fun j =>
           zsum len
             (fun l =>
                zmul (value (input_get n a j))
                  (zmul (value (input_get n b l))
                    (delta_nat i ((j + l) mod len)%nat)))).

    Lemma canonical_zip_mul_local :
      forall n (x y : tree int n),
        canonical_tree n x ->
        canonical_tree n y ->
        canonical_tree n (zip_tree n mul_mod x y).
    Proof.
      induction n as [|n IH]; intros x y Hx Hy.
      - simpl.
        apply canonical_mul_mod.
      - destruct x as [xl xr], y as [yl yr].
        simpl in *.
        destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
        split.
        + apply IH; assumption.
        + apply IH; assumption.
    Qed.

    Lemma ntt_fast_closed_form_local :
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
      change
        (Spect.T.value (Spect.T.output_get n (Spect.T.ntt_fast n t) k) =
         Spect.T.zsum (Spect.T.pow2 n)
           (fun j =>
              Spect.T.zmul (Spect.T.value (Spect.T.input_get n t j))
                (Spect.T.zpow (Spect.T.value (Spect.T.root n))
                   ((j * k)%nat)))).
      exact (Spect.ntt_fast_closed_form root_square root_half_neg n t k Ht Hk).
    Qed.

    Lemma intt_fast_closed_form_local :
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
      change
        (Spect.T.value (Spect.T.input_get n (Spect.T.intt_fast n t) i) =
         Spect.T.zmul (Spect.T.value (Spect.T.inv_pow2 n))
           (Spect.T.zsum (Spect.T.pow2 n)
             (fun k =>
                Spect.T.zmul (Spect.T.value (Spect.T.output_get n t k))
                  (Spect.T.zpow (Spect.T.value (Spect.T.inv_root n))
                     ((i * k)%nat))))).
      exact
        (Spect.intt_fast_closed_form inv_root_square inv_root_half_neg
           n t i Ht Hi).
    Qed.

    Theorem intt_fast_pointwise_mul_ntt_fast_cyclic_convolution :
      forall n (a b : tree int n) i,
        canonical_tree n a ->
        canonical_tree n b ->
        (i < pow2 n)%nat ->
        value
          (input_get n
            (intt_fast n
              (zip_tree n mul_mod (ntt_fast n a) (ntt_fast n b))) i) =
        cyclic_convolution_local n a b i.
    Proof.
      intros n a b i Ha Hb Hi.
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
        apply canonical_zip_mul_local; assumption.
      }
      change
        (value (input_get n (intt_fast n freq) i) =
         cyclic_convolution_local n a b i).
      rewrite (intt_fast_closed_form_local n freq i Hfreq Hi).
      subst freq.
      unfold cyclic_convolution_local.
      rewrite zsum_ext with
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
      rewrite zsum_ext with
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
        rewrite (ntt_fast_closed_form_local n a k Ha Hk).
        rewrite (ntt_fast_closed_form_local n b k Hb Hk).
        rewrite zmul_assoc.
        reflexivity.
      }
      rewrite zsum_ext with
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
        rewrite zsum_mul_const_r.
        subst sa.
        rewrite zsum_mul_expand.
        reflexivity.
      }
      rewrite zsum_swap.
      rewrite zsum_ext with
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
        rewrite zsum_swap.
        apply zsum_ext.
        intros l Hl.
        apply zsum_ext.
        intros k Hk.
        repeat rewrite <- zmul_assoc.
        f_equal.
        rewrite zmul_assoc.
        rewrite (zmul_comm (zpow (value (root n)) ((j * k)%nat))
                  (value (input_get n b l))).
        repeat rewrite <- zmul_assoc.
        reflexivity.
      }
      rewrite zsum_mul_const_l.
      apply zsum_ext.
      intros j Hj.
      rewrite zsum_mul_const_l.
      apply zsum_ext.
      intros l Hl.
      rewrite <- zsum_mul_const_l.
      rewrite <- zsum_mul_const_l.
      rewrite zmul_assoc.
      rewrite (zmul_comm (value (inv_pow2 n))
                (value (input_get n a j))).
      repeat rewrite <- zmul_assoc.
      f_equal.
      rewrite zmul_assoc.
      rewrite (zmul_comm (value (inv_pow2 n))
                (value (input_get n b l))).
      repeat rewrite <- zmul_assoc.
      rewrite (convolution_kernel n i j l Hi Hj Hl).
      reflexivity.
    Qed.
  End Kernel.
End TreeNTTKernel.
