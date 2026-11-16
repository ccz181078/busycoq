From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.

Section BouncerIncs.
Hypothesis tm:TM.
Hypothesis QL:Q.
Hypothesis w1 w2 w3 w4:list Sym.

Hypothesis LBouncerInc:
  forall l r m,
    l <* w1 <{{QL}} w2 *> w3^^m *> w4 *> r -[tm]->*
    l <{{QL}} w2 *> w3^^(1+m) *> w4 *> r.

Lemma LBouncerIncs:
  forall l r n m,
    l <* w1^^n <{{QL}} w2 *> w3^^m *> w4 *> r -[tm]->*
    l <{{QL}} w2 *> w3^^(n+m) *> w4 *> r.
Proof.
  intros.
  gen l r m.
  induction n; intros.
  - finish.
  - cbn[lpow].
    rewrite Str_app_assoc.
    follow LBouncerInc.
    follow IHn.
    finish.
Qed.

Lemma LBouncerIncs':
  forall l r n,
    l <* w1^^n <{{QL}} w2 *> w4 *> r -[tm]->*
    l <{{QL}} w2 *> w3^^n *> w4 *> r.
Proof.
  intros.
  follow (LBouncerIncs l r n 0).
  finish.
Qed.

End BouncerIncs.
