Require Import NArith.
Require Import PeanoNat.
Require Import Lia.
From BusyCoq Require Import LibTactics.

Inductive ternary :=
| xH0 | xH1
| m3a2(x:ternary)
| m3a3(x:ternary)
| m3a4(x:ternary)
.

Fixpoint to_nat(x:ternary):nat :=
match x with
| xH0 => 0%nat
| xH1 => 1%nat
| m3a2 x0 => 2+(to_nat x0)*3
| m3a3 x0 => 3+(to_nat x0)*3
| m3a4 x0 => 4+(to_nat x0)*3
end.

Fixpoint of_nat'(x sz:nat): ternary :=
match x with
| 0 => xH0
| 1 => xH1
| S (S x) =>
  match sz with
  | 0 => xH0
  | S sz =>
    match x mod 3 with
    | 0 => m3a2 (of_nat' (x/3) sz)
    | 1 => m3a3 (of_nat' (x/3) sz)
    | 2 => m3a4 (of_nat' (x/3) sz)
    | _ => xH0
    end
  end
end.

Definition of_nat(x:nat): ternary := of_nat' x x.

Lemma of_nat'_spec x sz:
  x <= sz ->
  of_nat' x sz = of_nat x.
Proof.
  gen sz.
  induction x using Wf_nat.lt_wf_ind.
  intros sz Hsz.
  destruct x as [|[|x]].
  1,2: destruct sz; reflexivity.
  destruct sz as [|sz].
  1: lia.
  cbn[of_nat'].
  pose proof (Nat.Div0.div_mod x 3) as Hx.
  unshelve epose proof (Nat.mod_upper_bound x 3 _) as Hx2.
  1: lia.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  unfold of_nat.
  replace (S x) with (x+1) by lia.
  cbn[of_nat'].
  replace (x+1) with (S x) by lia.
  rewrite <-Heqx1,<-Heqx2.
  destruct x2 as [|[|[|x2]]].
  4: lia.
  all: erewrite H; try lia;
    erewrite H; try lia;
    reflexivity.
Qed.

Lemma to_of_nat x:
  to_nat (of_nat x) = x.
Proof.
  induction x using Wf_nat.lt_wf_ind.
  destruct x as [|[|x]].
  1,2: reflexivity.
  pose proof (Nat.Div0.div_mod x 3) as Hx.
  unshelve epose proof (Nat.mod_upper_bound x 3 _) as Hx2.
  1: lia.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  unfold of_nat.
  replace (S x) with (x+1) by lia.
  cbn[of_nat'].
  replace (x+1) with (S x) by lia.
  rewrite <-Heqx1,<-Heqx2.
  destruct x2 as [|[|[|x2]]].
  4: lia.
  all: cbn[to_nat];
    rewrite of_nat'_spec; try lia;
    erewrite H; try lia.
Qed.

Lemma of_nat_m3a2 n:
  of_nat (2+n*3) = m3a2 (of_nat n).
Proof.
  change (of_nat (2+n*3)) with (of_nat' (S (S (n*3))) (S (1+n*3))).
  cbn[of_nat'].
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.div_mul. 2: lia.
  rewrite of_nat'_spec. 2: lia.
  reflexivity.
Qed.

Lemma of_nat_m3a3 n:
  of_nat (3+n*3) = m3a3 (of_nat n).
Proof.
  change (of_nat (3+n*3)) with (of_nat' (S (S (1+n*3))) (S (2+n*3))).
  cbn[of_nat'].
  rewrite Nat.Div0.mod_add.
  change (1 mod 3) with 1.
  cbn match.
  rewrite Nat.div_add. 2: lia.
  change (1 / 3) with 0.
  rewrite of_nat'_spec. 2: lia.
  reflexivity.
Qed.

Lemma of_nat_m3a4 n:
  of_nat (4+n*3) = m3a4 (of_nat n).
Proof.
  change (of_nat (4+n*3)) with (of_nat' (S (S (2+n*3))) (S (3+n*3))).
  cbn[of_nat'].
  rewrite Nat.Div0.mod_add.
  change (2 mod 3) with 2.
  cbn match.
  rewrite Nat.div_add. 2: lia.
  change (2 / 3) with 0.
  rewrite of_nat'_spec. 2: lia.
  reflexivity.
Qed.

Fixpoint succ x :=
match x with
| xH0 => xH1
| xH1 => m3a2 xH0
| m3a2 x0 => m3a3 x0
| m3a3 x0 => m3a4 x0
| m3a4 x0 => m3a2 (succ x0)
end.

Lemma succ_spec x:
  of_nat (S x) = succ (of_nat x).
Proof.
  induction x using Wf_nat.lt_wf_ind.
  destruct x as [|[|x]].
  1,2: reflexivity.
  pose proof (Nat.Div0.div_mod x 3) as Hx.
  unshelve epose proof (Nat.mod_upper_bound x 3 _) as Hx2.
  1: lia.
  remember (x/3) as x1.
  remember (x mod 3) as x2.
  destruct x2 as [|[|[|x2]]].
  4: lia.
  - replace (S(S(S x))) with (3+x1*3). 2: lia.
    replace (S(S x)) with (2+x1*3). 2: lia.
    rewrite of_nat_m3a3.
    rewrite of_nat_m3a2.
    reflexivity.
  - replace (S(S(S x))) with (4+x1*3). 2: lia.
    replace (S(S x)) with (3+x1*3). 2: lia.
    rewrite of_nat_m3a4.
    rewrite of_nat_m3a3.
    reflexivity.
  - replace (S(S(S x))) with (2+(S x1)*3). 2: lia.
    replace (S(S x)) with (4+x1*3). 2: lia.
    rewrite of_nat_m3a2.
    rewrite of_nat_m3a4.
    rewrite H. 2: lia.
    reflexivity.
Qed.

