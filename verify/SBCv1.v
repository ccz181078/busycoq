
From BusyCoq Require Import Individual62.
From BusyCoq Require Import BinaryCounterFull.
Require Import Lia.
Require Import ZArith.
Require Import String.
Set Default Goal Selector "!".






Section SBCv1.

Hypothesis tm:TM.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).


Hypothesis QL QR: Q.
Hypothesis d0 d1 d1' d1a d d': list Sym.
Hypothesis w0 w0' w10 w11: list Sym.
Hypothesis r0 r1: list Sym.


Fixpoint LeftBinaryCounter (n:positive) :=
match n with
| xH => d1a *> const 0
| xI n0 => d1 *> (LeftBinaryCounter n0)
| xO n0 => d0 *> (LeftBinaryCounter n0)
end.

Definition RightUnaryCounter_0 n m :=
  w0^^n *> w10 *> w0^^m *> const 0.

Definition RightUnaryCounter_1 n m :=
  w0^^n *> w11 *> w0^^m *> const 0.

Inductive Config :=
| Config_intro(n:positive)(m:nat)(Hf:full n)(H:m+2<=Pos.to_nat n).

Definition S0 n m :=
  (LeftBinaryCounter (xI n)) <{{QL}} d' *> RightUnaryCounter_0 (3+m) 0.

Definition to_config (x:Config) :=
  let (n,m,_,_):=x in S0 n m.

Hypothesis k0:positive.
Hypothesis k1:nat.
Hypothesis Hf_k0:full k0.
Hypothesis Hcmp_k0_k1: k1+2<=Pos.to_nat k0.
Definition cfg0 := Config_intro k0 k1 Hf_k0 Hcmp_k0_k1.
Hypothesis init':
  c0 -->*
  S0 k0 k1.



(*

sync bouncer counter
typical behavior version 1:

0^inf A> 0^inf --> 0^inf d1a d1^(i+1) <QL d' w0^(k1+3) 0^inf   (init)
k0 = 2^(i+1)-1
k1+2 <= k0

d1 <QL d' --> <QL d' d1' (L_carry)
d0 <QL d' --> d1 d QR>   (LR)
d QR> d1' --> d0 d QR>   (L_return)

d QR> w0 --> w0' d QR> (R_carry)
d QR> w10 w0 --> <QL d' w11 w0 (RL0)
d QR> w11 w0 --> <QL d' w0 w10 (RL1)
d QR> w10 0^inf --> <QL d' w0 w10 0^inf (RL2)
w0' <QL d' --> <QL d' w0 (R_return)


d1' = r0+r1 = r1+r0  (L_rotate)

0^inf d1a <QL d' r0 --> 0^inf d1a d0 d QR>   (L_overflow)
d QR> r1 w0 w0 --> <QL d' d1' w0 w10   (R_reset)

w10 0^inf = 0^inf   (R_w10_all0)
*)

Hypothesis L_carry:
  forall l r,
    l <* d1 <{{QL}} d' *> r -->*
    l <{{QL}} d' *> d1' *> r.

Hypothesis LR:
  forall l r,
    l <* d0 <{{QL}} d' *> r -->+
    l <* d1 <* d {{QR}}> r.

Hypothesis L_return:
  forall l r,
    l <* d {{QR}}> d1' *> r -->*
    l <* d0 <* d {{QR}}> r.

Hypothesis R_carry:
  forall l r,
  l <* d {{QR}}> w0 *> r -->*
  l <* w0' <* d {{QR}}> r.

Hypothesis RL0:
  forall l r,
  l <* d {{QR}}> w10 *> w0 *> r -->*
  l <{{QL}} d' *> w11 *> w0 *> r.

Hypothesis RL1:
  forall l r,
  l <* d {{QR}}> w11 *> w0 *> r -->*
  l <{{QL}} d' *> w0 *> w10 *> r.

Hypothesis RL2:
  forall l,
  l <* d {{QR}}> w10 *> const 0 -->*
  l <{{QL}} d' *> w0 *> w10 *> const 0.

Hypothesis R_return:
  forall l r,
  l <* w0' <{{QL}} d' *> r -->*
  l <{{QL}} d' *> w0 *> r.

Hypothesis L_rotate:
  d1' = (r0 ++ r1)%list.

Hypothesis L_rotate':
  d1' = (r1 ++ r0)%list.

Hypothesis L_overflow:
  forall r,
  const 0 <* d1a <{{QL}} d' *> r0 *> r -->*
  const 0 <* d1a <* d0 <* d {{QR}}> r.

Hypothesis R_reset:
  forall l r,
  l <* d {{QR}}> r1 *> w0 *> w0 *> r -->*
  l <{{QL}} d' *> d1' *> w0 *> w10 *> r.

Hypothesis R_w10_all0:
  w10 *> const 0 = const 0.





Lemma init:
  c0 -->*
  to_config cfg0.
Proof.
  apply init'.
Qed.


Lemma LInc n (Hnf:not_full n) r:
  (LeftBinaryCounter n) <{{QL}} d' *> r -->+
  (LeftBinaryCounter (n+1)) <* d {{QR}}> r.
Proof.
  gen r.
  induction Hnf; intro r.
  - apply LR.
  - cbn.
    follow L_carry.
    follow10 IHHnf.
    follow L_return.
    finish.
Qed.

Lemma LOverflow n (Hf:full n) r:
  (LeftBinaryCounter n) <{{QL}} d' *> d1' *> r -->*
  (LeftBinaryCounter (n+1)) <* d {{QR}}> r1 *> r.
Proof.
  gen r.
  induction Hf; intro r.
  - cbn.
    rewrite L_rotate.
    simpl_tape.
    apply L_overflow.
  - cbn.
    follow L_carry.
    follow IHHf.
    rewrite L_rotate.
    simpl_tape.
    replace (r1 *> r0 *> r1 *> r) with (d1' *> r1 *> r). 2:{
      rewrite L_rotate'.
      simpl_tape.
      reflexivity.
    }
    follow L_return.
    finish.
Qed.





Lemma R_carry' n l r:
  l <* d {{QR}}> w0^^n *> r -->*
  l <* w0'^^n <* d {{QR}}> r.
Proof.
  shift_rule.
  apply R_carry.
Qed.

Lemma R_return' n l r:
  l <* w0'^^n <{{QL}} d' *> r -->*
  l <{{QL}} d' *> w0^^n *> r.
Proof.
  shift_rule.
  apply R_return.
Qed.

Lemma RInc0 n m l:
  l <* d {{QR}}> RightUnaryCounter_0 n (S m) -->*
  l <{{QL}} d' *> RightUnaryCounter_1 n (S m).
Proof.
  unfold RightUnaryCounter_0,RightUnaryCounter_1.
  follow R_carry'.
  simpl_tape.
  follow RL0.
  follow R_return'.
  finish.
Qed.

Lemma RInc1 n m l:
  l <* d {{QR}}> RightUnaryCounter_1 n (S m) -->*
  l <{{QL}} d' *> RightUnaryCounter_0 (S n) m.
Proof.
  unfold RightUnaryCounter_0,RightUnaryCounter_1.
  follow R_carry'.
  simpl_tape.
  follow RL1.
  follow R_return'.
  rewrite lpow_shift'.
  finish.
Qed.

Lemma RInc2 n l:
  l <* d {{QR}}> RightUnaryCounter_0 n 0 -->*
  l <{{QL}} d' *> RightUnaryCounter_0 (S n) 0.
Proof.
  unfold RightUnaryCounter_0.
  follow R_carry'.
  follow RL2.
  follow R_return'.
  simpl_tape.
  finish.
Qed.


Lemma Overflow n (Hf:full n) m:
  (LeftBinaryCounter (xI n)) <{{QL}} d' *> RightUnaryCounter_0 (2+m) 0 -->*
  d *> LeftBinaryCounter (2*n+4) {{QR }}> RightUnaryCounter_0 1 m.
Proof.
  cbn.
  simpl_tape.
  follow L_carry.
  follow LOverflow.
  follow R_reset.
  replace (w0 *> w10 *> w0 ^^ m *> w10 *> const 0) with (RightUnaryCounter_0 1 m).
  2: {
    cbn; simpl_tape; cbn. 
    rewrite R_w10_all0.
    reflexivity.
  }
  follow100 (LInc (n+1) (full_S__not_full n Hf)).
  follow L_return.
  change (d0 *> LeftBinaryCounter (n+1+1)) with (LeftBinaryCounter (2*(n+1+1))).
  unfold RightUnaryCounter_0.
  simpl_tape.
  finish.
Qed.

Lemma Inc0 k (Hnf:not_full k) n m:
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_0 n (S m) -->+
  LeftBinaryCounter (k+1) <* d {{QR}}> RightUnaryCounter_1 n (S m).
Proof.
  follow RInc0.
  apply LInc,Hnf.
Qed.

Lemma Inc1 k (Hnf:not_full k) n m:
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_1 n (S m) -->+
  LeftBinaryCounter (k+1) <* d {{QR}}> RightUnaryCounter_0 (S n) m.
Proof.
  follow RInc1.
  apply LInc,Hnf.
Qed.

Lemma Inc2 k (Hnf:not_full k) n:
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_0 n O -->+
  LeftBinaryCounter (k+1) <* d {{QR}}> RightUnaryCounter_0 (S n) O.
Proof.
  follow RInc2.
  apply LInc,Hnf.
Qed.

Lemma Inc01 k (Hnf0:not_full k) (Hnf1:not_full (k+1)) n m:
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_0 n (1+m) -->+
  LeftBinaryCounter (k+2) <* d {{QR}}> RightUnaryCounter_0 (1+n) m.
Proof.
  follow11 (Inc0 k Hnf0 n m).
  follow10 (Inc1 (k+1) Hnf1 n m).
  finish.
Qed.

Lemma Inc01s c (Hf:full c) k n m i:
  (c<k)%positive ->
  (k+2*(Pos.of_succ_nat i)<=2*c+1)%positive ->
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_0 n (S (i+m)) -->+
  LeftBinaryCounter (k+2*(Pos.of_succ_nat i)) <* d {{QR}}> RightUnaryCounter_0 (S (i+n)) m.
Proof.
  intros H.
  gen m.
  induction i; intros m H0.
  - eapply (Inc01 k _ _ n m).
  - replace (S i + m) with (i + S m) by lia.
    epose proof (IHi (S m) _) as IHi'.
    follow11 IHi'.
    epose proof (Inc01 (k+2*Pos.of_succ_nat i) _ _ (S (i+n)) m) as H1.
    follow10 H1.
    finish.
  Unshelve.
  1,2,4,5: eapply (full_2n_not_full Hf).
  all: lia.
Qed.

Lemma Inc2s c (Hf:full c) k n i:
  (c<k)%positive ->
  (k+(Pos.of_succ_nat i)<=2*c+1)%positive ->
  LeftBinaryCounter (k) <* d {{QR}}> RightUnaryCounter_0 n O -->+
  LeftBinaryCounter (k+(Pos.of_succ_nat i)) <* d {{QR}}> RightUnaryCounter_0 (S (i+n)) O.
Proof.
  intros H.
  induction i; intros H0.
  - eapply (Inc2 k _ n).
  - epose proof (IHi _) as IHi'.
    follow11 IHi'.
    epose proof (Inc2 (k + Pos.of_succ_nat i) _ _) as H1.
    follow10 H1.
    finish.
  Unshelve.
    1,3: eapply (full_2n_not_full Hf).
    all: lia.
Qed.



Lemma BigStep n (Hf:full n) m:
  m+2<=Pos.to_nat n ->
  S0 n m -->+
  S0 (xI n) (2*(Pos.to_nat n)-m-3).
Proof.
  unfold S0.
  intro H.
  follow (Overflow n Hf (1+m)).
  epose proof (Inc01s _ (full_S _ Hf) _ _ O m _ _) as H1.
  replace (m+O) with m in H1 by lia.
  follow11 H1.
  epose proof (Inc2s _ (full_S _ Hf) _ _ (2*(Pos.to_nat n)-(2*m+4))%nat _ _) as H2.
  follow10 H2.
  follow RInc2.
  finish.
Unshelve.
  all: lia.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  apply progress_nonhalt_simple.
  intro i.
  destruct i as [n m Hf H].
  eexists (Config_intro (xI n) _ _ _).
  unfold to_config.
  apply (BigStep _ Hf _ H).
Unshelve.
  - constructor. apply Hf.
  - lia.
Qed.

End SBCv1.






Inductive SBC_cert_v1 :=
| Build_SBC_cert_v1
  (QL QR : Q)
  (d0 d1 d1' d1a d d' : list Sym)
  (w0 w0' w10 w11 : list Sym)
  (r0 r1 : list Sym)
  (n0: positive)
  (m0 : nat).


Ltac steps := cbn; intros;
  repeat ((try apply evstep_refl); (try apply evstep_refl); step).

Ltac solve_SBCv1 tm cert :=
match cert with
  (Build_SBC_cert_v1
  ?QL ?QR
  ?d0 ?d1 ?d1' ?d1a ?d ?d'
  ?w0 ?w0' ?w10 ?w11
  ?r0 ?r1
  ?n0 ?m0) =>
  eapply (nonhalt tm
    QL QR
    d0 d1 d1' d1a d d'
    w0 w0' w10 w11
    r0 r1
    n0 m0);
  [ repeat constructor
  | lia
  | unfold S0,LeftBinaryCounter,RightUnaryCounter_0;
    simpl_tape;
    steps
  | steps
  | execute
  | steps
  | steps
  | steps
  | steps
  | steps
  | steps
  | reflexivity
  | reflexivity
  | steps
  | steps
  | cbn;
    repeat rewrite <-const_unfold;
    reflexivity ]
end.














