From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.


Section FractalType1v1.

Hypothesis tm:TM.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Hypothesis QL QR: Q.
Hypothesis w1 w2 rL rR wL wR: list Sym.
Hypothesis cL cR:nat.

Hypothesis c1 c2:nat.
Hypothesis c3 c4 c5:nat.
Hypothesis y0:nat.

Hypothesis H_rL_all0:
  const 0 <* rL =
  const 0.

Hypothesis H_w2_all0:
  w2 *> const 0 =
  const 0.

(*

rL 0^inf = 0^inf  (H_rL_all0)
w2 0^inf = 0^inf  (H_w2_all0)

rL <QL wL --> <QL wL rR   (HL)
wR QR> rR --> rL wR QR>   (HR)

rL^cL w1 <QL wL --> w1 rL^cL wR QR>   (HLR)
wR QR> w2 rR^cR --> <QL wL rR^cR w2   (HRL)

rL^c1 wR QR> 0^inf --> w1 <QL wL rR^c2 0^inf   (HRL')
rL^(c3+c4) w1 w1 <QL wL --> rL^c4 w1 <QL wL rR^c2 w2 rR^c5   (HLL)

0^inf A> 0^inf --> 0^inf w1 <QL wL rR^c2 0^inf  (init)

cR = 1   (cR_def)
cL+c3 = c2+c5  (HE)
(c5+c1)*cL >= c4   (Hge)

rL^^(y0+cL) w1 <QL wL rR^c2 0^inf --> w1 <QL wL rR^(c1+y0) 0^inf   (Y_P1_O)

*)

Hypothesis HL:
  forall l r,
    l <* rL <{{QL}} wL  *> r -->*
    l <{{QL}} wL *> rR *> r.

Hypothesis HR:
  forall l r,
    l <* wR {{QR}}> rR *> r -->*
    l <* rL  <* wR {{QR}}> r.


Hypothesis HLR:
  forall l r,
    l <* rL^^cL <* w1 <{{QL}} wL *> r -->*
    l <* w1 <* rL^^cL <* wR {{QR}}> r.

Hypothesis HRL:
  forall l r,
    l <* wR {{QR}}> w2 *> rR^^cR *> r -->*
    l <{{QL}} wL *> rR^^cR *> w2 *> r.

Lemma HL' l r n:
  l <* rL^^n <{{QL}} wL *> r -->*
  l <{{QL}} wL *> rR^^n *> r.
Proof.
  shift_rule.
  apply HL.
Qed.

Lemma HR' l r n:
  l <* wR {{QR}}> rR^^n *> r -->*
  l <* rL^^n <* wR {{QR}}> r.
Proof.
  shift_rule.
  apply HR.
Qed.

Definition c := cL+cR.

Lemma Inc l r n:
  l <* rL^^cL <* w1 <{{QL}} wL *> rR^^n *> w2 *> rR^^cR *> r -->*
  l <* w1 <{{QL}} wL *> rR^^(n+c) *> w2 *> r.
Proof.
  follow HLR.
  follow HR'.
  follow HRL.
  follow HL'.
  follow HL'.
  unfold c.
  replace (n+(cL+cR)) with (cL+n+cR) by lia.
  simpl_tape.
  finish.
Qed.


Hypothesis HRL':
  forall l,
    l <* rL^^c1 <* wR {{QR}}> const 0 -->*
    l <* w1 <{{QL}} wL *> rR^^c2 *> const 0.

Hypothesis HLL:
  forall l r,
    l <* rL^^(c3+c4) <* w1 <* w1 <{{QL}} wL *> r -->+
    l <* rL^^c4 <* w1 <{{QL}} wL *> rR^^c2 *> w2 *> rR^^c5 *> r.


Hypothesis init:
  c0 -->*
  const 0 <* w1 <{{QL}} wL *> rR^^c2 *> const 0.

Hypothesis cR_def: cR = 1%nat.

Hypothesis HE:
  cL + c3 = c2 + c5.

Hypothesis Hge:
  (c5+c1)*cL >= c4.


Lemma Incs l n i:
  l <* rL^^(i*cL) <* w1 <{{QL}} wL *> rR^^n *> w2 *> rR^^(i*cR) *> const 0 -->*
  l <* w1 <{{QL}} wL *> rR^^(n+i*c) *> const 0.
Proof.
  gen l n.
  induction i; intros l n.
  - simpl_tape.
    rewrite H_w2_all0.
    finish.
  - simpl_tape.
    follow Inc.
    follow IHi.
    simpl_tape.
    finish.
Qed.


Lemma Reset l n:
  l <* rL^^cL <* w1 <{{QL}} wL *> rR^^(c1+n) *> const 0 -->*
  l <* w1 <* rL^^(n+cL) <* w1 <{{QL}} wL *> rR^^c2 *> const 0.
Proof.
  follow HLR.
  follow HR'.
  simpl_tape.
  follow HRL'.
  finish.
Qed.

Definition N (y:nat) :=
  (c2+c1*cL+(c5+y)*c).

Definition P1 (y:nat):=
  (forall l,
  l <* rL^^(y+cL) <* w1 <{{QL}} wL *> rR^^c2 *> const 0 -->*
  l <* w1 <{{QL}} wL *> rR^^(c1+y) *> const 0).


Lemma Incs' y:
  P1 y ->
  N y >= y /\
  forall l,
  l <* rL^^(N y-y) <* w1 <{{QL}} wL *> rR^^(c1+y) *> const 0 -->+
  l <* w1 <{{QL}} wL *> rR^^(c1+N y) *> const 0.
Proof.
  unfold P1.
  intros H.
  unfold N.
  split.
  1: unfold c; lia.
  intro l.

  replace (rL^^(c2+c1*cL+(c5+y)*c-y)) with
  (rL^^(cL+(c3+(c5+(c1+y))*cL))).
  2: {
    f_equal.
    unfold c.
    lia.
  }
  remember ((c5+(c1+y))*cL) as c'.
  replace (c3+c') with ((c3+c4)+(c'-c4)) by lia.
  remember (c3+c4) as c''.
  remember (y+cL) as x.
  replace (rL^^(cL+(c''+(c'-c4))) *> l)
  with (rL^^cL *> rL^^(c''+(c'-c4)) *> l) by (simpl_tape; reflexivity).
  follow Reset.
  rewrite <-Heqx.
  follow H.
  simpl_tape.
  follow10 HLL.
  replace (rR^^c5 *> rR^^c1 *> rR^^y *> const 0)
  with (rR^^((c5+(c1+y))*cR) *> const 0).
  2: {
    rewrite cR_def,Nat.mul_1_r.
    simpl_tape.
    reflexivity.
  }
  replace (rL^^c4 *> rL^^(c'-c4) *> l)
  with (rL^^c' *> l).
  2: {
    replace (rL^^c') with (rL^^(c4+(c'-c4))) by (f_equal; lia).
    simpl_tape.
    reflexivity.
  }
  subst c'.
  follow Incs.
  replace (c2+(c5+(c1+y))*c) with (c1+(c2+c1*cL+(c5+y)*c)).
  2: {
    unfold c.
    rewrite cR_def.
    lia.
  }
  simpl_tape.
  finish.
Qed.

Lemma Y_P1_S y:
  P1 y ->
  P1 (N y).
Proof.
  intro H.
  destruct (Incs' y H) as [H0 H1].
  unfold P1.
  unfold P1 in H.
  intros l.
  replace (N y + cL) with (y+cL+(N y-y)) by lia.
  remember (N y-y) as z.
  remember (y+cL) as z0.
  simpl_tape.
  follow H.
  follow100 H1.
  simpl_tape.
  finish.
Qed.


Hypothesis Y_P1_O:
  P1 y0.

Definition Y(n:nat):= Nat.iter n N y0.

Lemma Y_P1 n:
  P1 (Y n).
Proof.
  induction n.
  - apply Y_P1_O.
  - apply Y_P1_S,IHn.
Qed.

Definition to_config(n:nat) :=
  const 0 <* w1 <{{QL}} wL *> rR^^(c1+Y n) *> const 0.

Lemma rL_pow_all0 n:
  rL^^n *> const 0 =
  const 0.
Proof.
  induction n.
  - reflexivity.
  - simpl_tape.
    rewrite IHn.
    apply H_rL_all0.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=to_config O).
  1: {
    follow init.
    unfold to_config.
    specialize (Y_P1_O (const 0)).
    rewrite rL_pow_all0 in Y_P1_O.
    apply Y_P1_O.
  }
  apply progress_nonhalt_simple.
  intro i.
  exists (S i).
  unfold to_config.
  destruct (Incs' (Y i) (Y_P1 i)) as [H0 H1].
  specialize (H1 (const 0)).
  rewrite rL_pow_all0 in H1.
  apply H1.
Qed.

End FractalType1v1.


Inductive FractalType1_cert_v1 :=
| Build_FractalType1_cert_v1
  (QL QR : Q)
  (w1 w2 rL rR wL wR : list Sym)
  (cL cR c1 c2 c3 c4 c5 y0 : nat).


Ltac solve_FractalType1v1 tm cert :=
match cert with
  (Build_FractalType1_cert_v1
  ?QL ?QR
  ?w1 ?w2 ?rL ?rR ?wL ?wR
  ?cL ?cR ?c1 ?c2 ?c3 ?c4 ?c5 ?y0) =>
  apply (nonhalt tm
    QL QR
    w1 w2 rL rR wL wR
    cL cR c1 c2 c3 c4 c5 y0);
  [ cbn; repeat rewrite <-const_unfold; reflexivity
  | cbn; repeat rewrite <-const_unfold; reflexivity
  | steps
  | steps
  | steps
  | steps
  | steps
  | execute
  | steps
  | reflexivity
  | reflexivity
  | lia
  | unfold P1; steps ]
end.



