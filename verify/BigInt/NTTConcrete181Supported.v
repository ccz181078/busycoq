From Coq Require Import Lia.
Require Import BigInt.NTTConcrete BigInt.NTTKernelBounded BigInt.BigIntMul
  BigInt.NTTConcrete181Squares BigInt.NTTConcrete181Inverse BigInt.NTTConcrete181InvPow2.

Module Prime181KBSupported := TreeNTTKernelBounded(Prime181Cfg).
Module Prime181SupportedFacts.
  Module T := Prime181KBSupported.T.
  Module K := Prime181KBSupported.K.
  Module Spect := Prime181KBSupported.Spect.
  Module Sq := Prime181SquareFacts.
  Module Inv := Prime181InverseFacts.
  Module Pow := Prime181InvPow2Facts.
  Import T Spect.

  Lemma root_square_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (root (S n))) 2%nat = value (root n).
  Proof.
    exact Sq.root_square_upto.
  Qed.

  Lemma inv_root_square_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (inv_root (S n))) 2%nat = value (inv_root n).
  Proof.
    exact Sq.inv_root_square_upto.
  Qed.

  Lemma root_inv_mul_one_upto :
    forall n, (n <= S supported_max_log)%nat ->
      zmul (value (root n)) (value (inv_root n)) = zone.
  Proof.
    exact Inv.root_inv_mul_one_upto.
  Qed.

  Lemma inv_pow2_zero :
    value (inv_pow2 0%nat) = zone.
  Proof.
    exact Pow.inv_pow2_zero.
  Qed.

  Lemma inv_pow2_double_upto :
    forall n, (n < S supported_max_log)%nat ->
      zadd (value (inv_pow2 (S n))) (value (inv_pow2 (S n))) = value (inv_pow2 n).
  Proof.
    exact Pow.inv_pow2_double_upto.
  Qed.

  Lemma root1_neg :
    value (root 1%nat) = zminus_one.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma inv_root1_neg :
    value (inv_root 1%nat) = zminus_one.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma root0_one :
    value (root 0%nat) = zone.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma root_half_neg_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (root (S n))) (pow2 n) = zminus_one.
  Proof.
    induction n as [|n IH]; intros Hn.
    - exact root1_neg.
    - rewrite pow2_succ.
      replace (pow2 n + pow2 n)%nat with (2 * pow2 n)%nat by lia.
      rewrite zpow_mul.
      rewrite root_square_upto by lia.
      apply IH.
      lia.
  Qed.

  Lemma inv_root_half_neg_upto :
    forall n, (n < S supported_max_log)%nat ->
      zpow (value (inv_root (S n))) (pow2 n) = zminus_one.
  Proof.
    induction n as [|n IH]; intros Hn.
    - exact inv_root1_neg.
    - rewrite pow2_succ.
      replace (pow2 n + pow2 n)%nat with (2 * pow2 n)%nat by lia.
      rewrite zpow_mul.
      rewrite inv_root_square_upto by lia.
      apply IH.
      lia.
  Qed.

  Lemma root_period_upto :
    forall n, (n <= S supported_max_log)%nat ->
      zpow (value (root n)) (pow2 n) = zone.
  Proof.
    induction n as [|n IH]; intros Hn.
    - change (pow2 0%nat) with 1%nat.
      rewrite zpow_1.
      exact root0_one.
    - rewrite pow2_succ.
      replace (pow2 n + pow2 n)%nat with (2 * pow2 n)%nat by lia.
      rewrite zpow_mul.
      rewrite root_square_upto by lia.
      apply IH.
      lia.
  Qed.

  Lemma inv_root_as_root_pred_upto :
    forall n, (n <= S supported_max_log)%nat ->
      value (inv_root n) =
      zpow (value (root n)) (Nat.pred (pow2 n)).
  Proof.
    intros [|n] Hn.
    - vm_compute.
      reflexivity.
    - set (r := value (root (S n))).
      set (ir := value (inv_root (S n))).
      replace (Nat.pred (pow2 (S n))) with ((pow2 (S n) - 1)%nat).
      2:{
        pose proof (pow2_pos (S n)) as Hpos.
        lia.
      }
      assert (Hir : zcanon ir = ir).
      {
        subst ir.
        apply zcanon_small.
        apply Prime181Cfg.inv_root_range.
      }
      assert (Hr : zcanon r = r).
      {
        subst r.
        apply zcanon_small.
        apply Prime181Cfg.root_range.
      }
      assert (Hperiod : zpow r (pow2 (S n)) = zone).
      {
        subst r.
        apply root_period_upto.
        lia.
      }
      assert (Hinv : zmul r ir = zone).
      {
        subst r ir.
        apply root_inv_mul_one_upto.
        lia.
      }
      transitivity (zmul ir zone).
      {
        rewrite zmul_comm.
        rewrite zmul_1_l.
        symmetry.
        exact Hir.
      }
      rewrite <- Hperiod.
      replace (pow2 (S n)) with ((pow2 (S n) - 1 + 1)%nat).
      2:{
        pose proof (pow2_pos (S n)) as Hpos.
        lia.
      }
      rewrite zpow_add.
      rewrite zpow_1.
      rewrite Hr.
      rewrite zmul_assoc.
      rewrite (zmul_comm ir (zpow r (pow2 (S n) - 1))).
      repeat rewrite <- zmul_assoc.
      rewrite (zmul_comm ir r).
      rewrite Hinv.
      rewrite K.zmul_1_r.
      replace (pow2 (S n) - 1 + 1 - 1)%nat with (pow2 (S n) - 1)%nat by lia.
      apply zpow_canon.
  Qed.
End Prime181SupportedFacts.
