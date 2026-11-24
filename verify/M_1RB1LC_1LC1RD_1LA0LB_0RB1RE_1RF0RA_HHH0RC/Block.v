(** Many visits at once (port of lean/Block.lean): a formal run of grow/swap digits on integers that ends with
    both coordinates at least 16 * 2^K is the orbit of [op] for those K visits. *)
From Coq Require Import ZArith Lia List.
From BusyCoq.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC Require Import Visits.
Import ListNotations.
Local Open Scope Z_scope.

Definition dstep (g : bool) (x : Z * Z) : Z * Z :=
  let (a, b) := x in
  if g then (if Z.even a then (2 * a + 4, b - a - 1) else (2 * a + 3, b - a)) else (a - b + 1, 2 * b + 3).

Fixpoint drun (L : list bool) (x : Z * Z) : Z * Z :=
  match L with [] => x | g :: L => drun L (dstep g x) end.

Lemma drun_app L1 L2 x : drun (L1 ++ L2) x = drun L2 (drun L1 x).
Proof. revert x. induction L1; intros x; [reflexivity|]. apply IHL1. Qed.

Lemma dstep_sum g a b : fst (dstep g (a, b)) + snd (dstep g (a, b)) >= a + b + 3.
Proof. destruct g; cbn [dstep fst snd]; [destruct (Z.even a)|]; cbn [fst snd]; lia. Qed.

Lemma dstep_min g a b T : 0 <= a + b -> T <= fst (dstep g (a, b)) -> T <= snd (dstep g (a, b)) ->
  T <= 2 * a + 4 /\ T <= 2 * b + 4.
Proof. intros. destruct g; cbn [dstep fst snd] in *; [destruct (Z.even a)|]; cbn [fst snd] in *; lia. Qed.

Lemma drun_back L : forall a b X, 0 <= a + b ->
  2 ^ Z.of_nat (length L) * (X + 4) <= fst (drun L (a, b)) + 4 ->
  2 ^ Z.of_nat (length L) * (X + 4) <= snd (drun L (a, b)) + 4 -> X <= a /\ X <= b.
Proof.
  induction L as [|g L IH]; intros a b X Hs H1 H2; cbn [drun length] in *.
  - cbn [length Z.of_nat drun fst snd] in *. rewrite Z.pow_0_r in *. lia.
  - destruct (dstep g (a, b)) as [a1 b1] eqn:Hf.
    pose proof (dstep_sum g a b) as S1. rewrite Hf in S1. cbn [fst snd] in S1.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in H1, H2 by lia.
    assert (E : 2 * 2 ^ Z.of_nat (length L) * (X + 4) = 2 ^ Z.of_nat (length L) * ((2 * X + 4) + 4)) by ring.
    rewrite E in H1, H2.
    destruct (IH a1 b1 (2 * X + 4) ltac:(lia) H1 H2) as [K1 K2].
    pose proof (dstep_min g a b (2 * X + 4) Hs) as M. rewrite Hf in M. cbn [fst snd] in M. specialize (M K1 K2). lia.
Qed.

Lemma Zeven_of_nat n : Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite Nat2Z.inj_succ, Z.even_succ, Nat.even_succ, <- Z.negb_even, <- Nat.negb_even, IH. reflexivity.
Qed.

Lemma dstep_op g (a b : nat) :
  28 <= fst (dstep g (Z.of_nat a, Z.of_nat b)) -> 28 <= snd (dstep g (Z.of_nat a, Z.of_nat b)) ->
  op (a, b) = Some (Z.to_nat (fst (dstep g (Z.of_nat a, Z.of_nat b))), Z.to_nat (snd (dstep g (Z.of_nat a, Z.of_nat b)))).
Proof.
  intros H1 H2. unfold op.
  destruct g; cbn [dstep fst snd] in *.
  - rewrite Zeven_of_nat in *.
    destruct (Nat.even a) eqn:Ev; cbn [fst snd] in *.
    + destruct (Nat.eqb_spec b 3); [lia|]. destruct (Nat.eqb_spec b 2); [lia|].
      destruct (Nat.leb_spec b a); [lia|]. destruct (Nat.eqb_spec b (a + 1)); [lia|].
      destruct (Nat.eqb_spec b (a + 2)); [lia|]. f_equal; f_equal; lia.
    + destruct (Nat.eqb_spec b 3); [lia|]. destruct (Nat.eqb_spec b 2); [lia|].
      destruct (Nat.leb_spec b a); [lia|]. destruct (Nat.eqb_spec b (a + 1)); [lia|].
      destruct (Nat.eqb_spec b (a + 2)); [lia|]. destruct (Nat.eqb_spec b (a + 3)); [lia|].
      f_equal; f_equal; lia.
  - destruct (Nat.eqb_spec b 3); [lia|]. destruct (Nat.eqb_spec b 2); [lia|].
    destruct (Nat.leb_spec b a); [|lia]. f_equal; f_equal; lia.
Qed.

(** The block check: whatever the digits, a formal run ending with both coordinates at least 16 * 2^K is the next
    K visits. *)
Theorem block_ok L : forall (a b : nat),
  16 * 2 ^ Z.of_nat (length L) <= fst (drun L (Z.of_nat a, Z.of_nat b)) ->
  16 * 2 ^ Z.of_nat (length L) <= snd (drun L (Z.of_nat a, Z.of_nat b)) ->
  opIter (length L) (a, b) =
    Some (Z.to_nat (fst (drun L (Z.of_nat a, Z.of_nat b))), Z.to_nat (snd (drun L (Z.of_nat a, Z.of_nat b)))).
Proof.
  induction L as [|g L IH]; intros a b H1 H2; cbn [drun length opIter] in *.
  - cbn [fst snd]. rewrite !Nat2Z.id. reflexivity.
  - destruct (dstep g (Z.of_nat a, Z.of_nat b)) as [a1 b1] eqn:Hf.
    pose proof (dstep_sum g (Z.of_nat a) (Z.of_nat b)) as S1. rewrite Hf in S1. cbn [fst snd] in S1.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in H1, H2 by lia.
    pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (length L)) ltac:(lia) ltac:(lia)) as Hp.
    destruct (drun_back L a1 b1 28 ltac:(lia) ltac:(lia) ltac:(lia)) as [K1 K2].
    pose proof (dstep_op g a b) as O. rewrite Hf in O. cbn [fst snd] in O. rewrite (O K1 K2).
    replace a1 with (Z.of_nat (Z.to_nat a1)) in * by lia. replace b1 with (Z.of_nat (Z.to_nat b1)) in * by lia.
    rewrite !Nat2Z.id. apply IH; lia.
Qed.
