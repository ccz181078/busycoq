From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.

Lemma lpow_fold_1 (a:Sym) n r:
  a >> [a]^^n *> r =
  [a]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  cbn.
  rewrite lpow_rotate.
  reflexivity.
Qed.

Lemma lpow_fold_2 (a b:Sym) n r:
  a >> b >> [a;b]^^n *> r =
  [a;b]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 2 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_fold_3 (a b c:Sym) n r:
  a >> b >> c >> [a;b;c]^^n *> r =
  [a;b;c]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 3 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_fold_4 (a b c d:Sym) n r:
  a >> b >> c >> d >> [a;b;c;d]^^n *> r =
  [a;b;c;d]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 4 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_fold_5 (a b c d e:Sym) n r:
  a >> b >> c >> d >> e >> [a;b;c;d;e]^^n *> r =
  [a;b;c;d;e]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 5 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_fold_6 (a b c d e f:Sym) n r:
  a >> b >> c >> d >> e >> f >> [a;b;c;d;e;f]^^n *> r =
  [a;b;c;d;e;f]^^(n+1) *> r.
Proof.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  do 6 (cbn; rewrite lpow_rotate).
  reflexivity.
Qed.

Lemma lpow_all0_1 n:
  [0]^^n *> const 0 = const 0.
Proof.
  rewrite lpow_all0; solve_const0_eq.
Qed.

Lemma lpow_all0_2 n:
  [0;0]^^n *> const 0 = const 0.
Proof.
  rewrite lpow_all0; solve_const0_eq.
Qed.

Lemma lpow_all0_3 n:
  [0;0;0]^^n *> const 0 = const 0.
Proof.
  rewrite lpow_all0; solve_const0_eq.
Qed.

Lemma simpl_nat_add1 a b c:
  (a+(S b)+(S c)) = (a+(S(S b))+c).
Proof. lia. Qed.

Ltac fold_tape :=
  repeat rewrite lpow_fold_1 in *;
  repeat rewrite lpow_fold_2 in *;
  repeat rewrite lpow_fold_3 in *;
  repeat rewrite lpow_fold_4 in *;
  repeat rewrite lpow_fold_5 in *;
  repeat rewrite lpow_fold_6 in *;
  repeat rewrite lpow_add' in *;
  repeat (
  rewrite simpl_nat_add1 in * ||
  rewrite Nat.add_0_r in *).

Ltac simpl_lpow_all0 :=
  repeat (
  rewrite lpow_all0_1 in * ||
  rewrite lpow_all0_2 in * ||
  rewrite lpow_all0_3 in * ||
  rewrite <-const_unfold in *).


