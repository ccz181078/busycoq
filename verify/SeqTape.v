From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.


Open Scope list.

Notation "a ^^^ b" := (flat_map a b) (at level 20, no associativity).

Fixpoint arith_seq_inc(a0 n a:nat):=
match n with
| O => nil
| S n0 => a0 :: arith_seq_inc (a+a0) n0 a
end.

Fixpoint arith_seq_dec(a0 n a:nat):=
match n with
| O => nil
| S n0 => a0 :: arith_seq_dec (a0-a) n0 a
end.


Lemma arith_seq_dec_tail a0 n a:
  a*n <= a0 ->
  arith_seq_dec a0 (S n) a =
  (arith_seq_dec a0 n a) ++ [a0-a*n].
Proof.
  gen a0.
  induction n; intros.
  - cbn. f_equal. lia.
  - cbn.
    cbn in IHn.
    specialize (IHn (a0-a)).
    rewrite IHn.
    2: lia.
    repeat (f_equal; try lia).
Qed.





Lemma even_mul2 n:
  Nat.even (n*2) = true.
Proof.
  rewrite Nat.even_spec; exists n; lia.
Qed.

Lemma odd_mul2add1 n:
  Nat.even (1+n*2) = false.
Proof.
  cbn[Nat.add].
  rewrite Nat.even_succ.
  unfold Nat.odd.
  rewrite even_mul2.
  reflexivity.
Qed.

Lemma even_div2 n:
  if Nat.even n then n = n/2*2 else n=n/2*2+1.
Proof.
  induction n.
  1: reflexivity.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  destruct (Nat.even n); cbn[negb].
  - replace (S n) with (1+n) by lia.
    remember (n/2) as n0. clear Heqn0.
    subst n.
    rewrite Nat.div_add; cbn; lia.
  - replace (S n) with (1+n) by lia.
    remember (n/2) as n0. clear Heqn0.
    subst n.
    replace (1+(n0*2+1)) with (2+n0*2) by lia.
    rewrite Nat.div_add; cbn; lia.
Qed.

Lemma even_S_div2 n:
  Nat.even n = true -> n/2 = (S n)/2.
Proof.
  pose proof (even_div2 n) as H.
  intro H0.
  rewrite H0 in H.
  remember (n/2) as n0.
  rewrite H.
  replace (S (n0*2)) with (1+n0*2) by lia.
  rewrite Nat.div_add; cbn; lia.
Qed.

Lemma odd_S_div2 n:
  Nat.even n = false -> S (n/2) = (S n)/2.
Proof.
  pose proof (even_div2 n) as H.
  intro H0.
  rewrite H0 in H.
  remember (n/2) as n0.
  rewrite H.
  replace (S (n0*2+1)) with (2+n0*2) by lia.
  rewrite Nat.div_add; cbn; lia.
Qed.


Lemma pow2sub1_odd n:
  Nat.even (2^(S n)-1) = false.
Proof.
  cbn.
  pose proof (Nat.pow_nonzero 2 n).
  replace (2^n+(2^n+0)-1) with (S (2*(2^n-1))) by lia.
  rewrite Nat.even_succ.
  unfold Nat.odd.
  rewrite Bool.negb_false_iff.
  rewrite Nat.even_spec.
  eexists _.
  f_equal.
Qed.

Lemma pow2sub1_div2 n:
  (2^(S n)-1)/2 = 2^n-1.
Proof.
  cbn[Nat.pow].
  pose proof (Nat.pow_nonzero 2 n).
  replace (2*2^n-1) with ((2^n-1)*2+1) by lia.
  rewrite Nat.div_add_l; cbn; lia.
Qed.

