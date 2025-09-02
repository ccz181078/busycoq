Require Import PeanoNat ZifyNat Lia.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Ltac lia' := rw_pa; lia.

Lemma add_sub_lt a b c v1:
  b<c ->
  v1=c-b ->
  a+b-c = a-v1.
Proof. lia. Qed.

Lemma add_sub_ge a b c v1:
  c<=b ->
  v1=b-c ->
  a+b-c = a+v1.
Proof. lia. Qed.

Lemma sub_add_le a b c v1:
  b<=c ->
  b<=a ->
  v1=c-b ->
  a-b+c = a+v1.
Proof. lia. Qed.

Lemma sub_add_gt a b c v1:
  c<b ->
  b<=a ->
  v1=b-c ->
  a-b+c = a-v1.
Proof. lia. Qed.

Lemma add_add a b c v1:
  v1=b+c ->
  a+b+c = a+v1.
Proof. lia. Qed.

Lemma sub_sub a b c v1:
  v1=b+c ->
  a-b-c = a-v1.
Proof. lia. Qed.

Lemma pow2sub_mul2 a b c v1:
  v1=c*2 ->
  (2^(a+b)-c)*2 = 2^(a+S b)-v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2add_mul2 a b c v1:
  v1=c*2 ->
  (2^(a+b)+c)*2 = 2^(a+S b)+v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2sub_div2 a b c v1:
  v1=(S c)/2 ->
  (2^(a+S b)-c)/2 = 2^(a+b)-v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2add_div2 a b c v1:
  v1=c/2 ->
  (2^(a+S b)+c)/2 = 2^(a+b)+v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2sub_mul2_O b c v1:
  v1=c*2 ->
  (2^(b)-c)*2 = 2^(S b)-v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2add_mul2_O b c v1:
  v1=c*2 ->
  (2^(b)+c)*2 = 2^(S b)+v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2sub_div2_O b c v1:
  v1=(S c)/2 ->
  (2^(S b)-c)/2 = 2^(b)-v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma pow2add_div2_O b c v1:
  v1=c/2 ->
  (2^(S b)+c)/2 = 2^(b)+v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2sub_mul2 k a b c v1:
  v1=c*2 ->
  (k*2^(a+b)-c)*2 = k*2^(a+S b)-v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2add_mul2 k a b c v1:
  v1=c*2 ->
  (k*2^(a+b)+c)*2 = k*2^(a+S b)+v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2sub_div2 k a b c v1:
  v1=(S c)/2 ->
  (k*2^(a+S b)-c)/2 = k*2^(a+b)-v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2add_div2 k a b c v1:
  v1=c/2 ->
  (k*2^(a+S b)+c)/2 = k*2^(a+b)+v1.
Proof.
  rewrite Nat.add_succ_r.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2sub_mul2_O k b c v1:
  v1=c*2 ->
  (k*2^(b)-c)*2 = k*2^(S b)-v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2add_mul2_O k b c v1:
  v1=c*2 ->
  (k*2^(b)+c)*2 = k*2^(S b)+v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2sub_div2_O k b c v1:
  v1=(S c)/2 ->
  (k*2^(S b)-c)/2 = k*2^(b)-v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2add_div2_O k b c v1:
  v1=c/2 ->
  (k*2^(S b)+c)/2 = k*2^(b)+v1.
Proof.
  cbn[Nat.pow].
  lia.
Qed.

Lemma mulpow2_O a:
  a*2^0 = a.
Proof.
  lia.
Qed.

Ltac is_cnat a :=
match a with
| S ?a0 => is_cnat a0
| O => idtac
end.

Ltac crefl := vm_compute; reflexivity.

Ltac simpl_nat :=
  repeat
  match goal with
  | |- context[?a+?b-?c] =>
    is_cnat b;
    is_cnat c;
    ((erewrite (add_sub_lt a b c); [|lia|crefl]) +
     (erewrite (add_sub_ge a b c); [|lia|crefl]))
  | |- context[?a-?b+?c] =>
    is_cnat b;
    is_cnat c;
    ((erewrite (sub_add_le a b c); [|lia|lia'|crefl]) +
     (erewrite (sub_add_gt a b c); [|lia|lia'|crefl]))
  | |- context[?a+?b+?c] =>
    is_cnat b;
    is_cnat c;
    (erewrite (add_add a b c); [|crefl])
  | |- context[?a-?b-?c] =>
    is_cnat b;
    is_cnat c;
    (erewrite (sub_sub a b c); [|crefl])
  | |- context[(2^(?a+?b)+?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2add_mul2 a b c); [|crefl])
  | |- context[(2^(?a+?b)-?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2sub_mul2 a b c); [|crefl])
  | |- context[(2^(?a+S ?b)+?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2add_div2 a b c); [|crefl])
  | |- context[(2^(?a+S ?b)-?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2sub_div2 a b c); [|crefl])
  | |- context[(2^(?b)+?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2add_mul2_O b c); [|crefl])
  | |- context[(2^(?b)-?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2sub_mul2_O b c); [|crefl])
  | |- context[(2^(S ?b)+?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2add_div2_O b c); [|crefl])
  | |- context[(2^(S ?b)-?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (pow2sub_div2_O b c); [|crefl])
  | |- context[(?k*2^(?a+?b)+?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2add_mul2 k a b c); [|crefl])
  | |- context[(?k*2^(?a+?b)-?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2sub_mul2 k a b c); [|crefl])
  | |- context[(?k*2^(?a+S ?b)+?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2add_div2 k a b c); [|crefl])
  | |- context[(?k*2^(?a+S ?b)-?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2sub_div2 k a b c); [|crefl])
  | |- context[(?k*2^(?b)+?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2add_mul2_O k b c); [|crefl])
  | |- context[(?k*2^(?b)-?c)*2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2sub_mul2_O k b c); [|crefl])
  | |- context[(?k*2^(S ?b)+?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2add_div2_O k b c); [|crefl])
  | |- context[(?k*2^(S ?b)-?c)/2] =>
    is_cnat b;
    is_cnat c;
    (erewrite (mulpow2sub_div2_O k b c); [|crefl])
  | |- context[?a*2^O] =>
    rewrite (mulpow2_O a)
  | |- context[?a+?b] =>
    is_cnat a;
    is_cnat b;
    eassert (a+b=_) as H_rw by crefl;
    rewrite H_rw;
    clear H_rw
  | |- context[?a-?b] =>
    is_cnat a;
    is_cnat b;
    eassert (a-b=_) as H_rw by crefl;
    rewrite H_rw;
    clear H_rw
  | |- context[?a*?b] =>
    is_cnat a;
    is_cnat b;
    eassert (a*b=_) as H_rw by crefl;
    rewrite H_rw;
    clear H_rw
  | |- context[?a/?b] =>
    is_cnat a;
    is_cnat b;
    eassert (a/b=_) as H_rw by crefl;
    rewrite H_rw;
    clear H_rw
  end.
