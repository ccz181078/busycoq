From Coq Require Import ZArith Lia.
Require Import BigInt.NTTTree.

Local Open Scope Z_scope.

Module TreeNTTConvolution (C : NTTBaseCfg).
  Module T := TreeNTT(C).
  Import T.

  Definition pointwise_mul_tree (n : nat) : tree int n -> tree int n -> tree int n :=
    zip_tree n mul_mod.

  Definition delta_nat (i j : nat) : Z :=
    if Nat.eqb i j then zone else zzero.

  Definition cyclic_convolution (n : nat) (a b : tree int n) (i : nat) : Z :=
    let len := pow2 n in
    zsum len
      (fun j =>
         zsum len
           (fun l =>
              zmul (value (input_get n a j))
                (zmul (value (input_get n b l))
                  (delta_nat i ((j + l) mod len)%nat)))).

  Lemma zcanon_0 : zcanon 0 = 0.
  Proof.
    unfold zcanon.
    apply Z.mod_small.
    split.
    - lia.
    - exact modulus_pos.
  Qed.

  Lemma zadd_0_r : forall x, zadd x zzero = zcanon x.
  Proof.
    intro x.
    rewrite zadd_comm.
    apply zadd_0_l.
  Qed.

  Lemma zmul_1_r : forall x, zmul x zone = zcanon x.
  Proof.
    intro x.
    rewrite zmul_comm.
    apply zmul_1_l.
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

  Lemma zsum_zero :
    forall n, zsum n (fun _ => zzero) = zzero.
  Proof.
    induction n as [|n IH].
    - reflexivity.
    - simpl.
      rewrite IH.
      apply zadd_0_r.
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

  Lemma canonical_zip_mul :
    forall n (x y : tree int n),
      canonical_tree n x ->
      canonical_tree n y ->
      canonical_tree n (pointwise_mul_tree n x y).
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

  Lemma canonical_ntt_fast :
    forall n (t : tree int n),
      canonical_tree n t ->
      canonical_tree n (ntt_fast n t).
  Proof.
    intros n t Ht.
    rewrite ntt_fast_eq by exact Ht.
    apply canonical_ntt.
    exact Ht.
  Qed.

End TreeNTTConvolution.
