From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import BinaryCounter_v2.
From BusyCoq Require Import Longitudinal.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LD_1RC0RE_0LA0RC_1LB1LD_0LF1RE_---1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition S1 l a b c :=
  l <* [1]^^a <{{B}} [1]^^b *> [1;0]^^(1+c) *> 0inf.

Lemma Inc1 l a b c:
  S1 l (1+a) (1+b) c -->*
  S1 l a b (1+c).
Proof.
  es.
Qed.

Lemma Incs1 n l a b c:
  S1 l (n+a) (n+b) c -->*
  S1 l a b (n+c).
Proof.
  gen a b c.
  ind n Inc1.
Qed.

Notation "l <| r" := (l <{{D}} r) (at level 30).

Lemma Inc_a l a b:
  a<=b ->
  l <* [0] <* [1]^^a <* [0] <* [1]^^b <| 0inf -->*
  l<*[1]<*[0]^^(b-a)<*[1]^^(a*2+1) <| 0inf.
Proof.
  intros.
  mid (S1 (l<<0) a b 0).
  1: es.
  mid (S1 (l<<0) (a+0) (a+(b-a)) 0).
  1: finish.
  follow Incs1.
  es.
Qed.

Lemma Inc_b l a b:
  b<a ->
  halts tm (l <* [0] <* [1]^^a <* [0] <* [1]^^b <| 0inf).
Proof.
  intros.
  eapply halts_evstep.
  2:{
  mid (S1 (l<<0) a b 0).
  1: es.
  mid (S1 (l<<0) (b+(1+(a-b-1))) (b+0) 0).
  1: finish.
  follow Incs1.
  finish.
  }
  esx.
Qed.

Open Scope nat.

Inductive P: (nat*nat+nat*nat)->(nat*nat+nat)->Prop :=
| P1 a b c:
  a <= b ->
  P (inr (b-a,a*2+1)) (inr (c)) ->
  P (inl (a,b)) (inr (1+c))
| P2 a b c d:
  a <= b ->
  P (inr (b-a,a*2+1)) (inl (c,d)) ->
  P (inl (a,b)) (inl (1+c,d))
| P3 b:
  P (inr (0,b)) (inr b)
| P4 a b c:
  P (inr (a,b)) (inr c) ->
  P (inr (1+a,b)) (inl (0,c))
| P5 a b x0 x:
  P (inr (a,b)) (inl x0) ->
  P (inl x0) x ->
  P (inr (1+a,b)) x
.

Close Scope nat.

Lemma P_spec x y:
  P x y ->
  forall l,
  match x with
  | inl (a,b) => l <* [0] <* [1]^^a <* [0] <* [1]^^b <| 0inf
  | inr (a,b) => l <* [0]^^a <* [1]^^b <| 0inf
  end -->*
  match y with
  | inl (c,d) => l <* [1]^^c <* [0] <* [1]^^d <| 0inf
  | inr (c) => l <* [1]^^c <| 0inf
  end.
Proof.
  intros HP.
  induction HP; intros.
  - follow Inc_a.
    follow.
    es.
  - follow Inc_a.
    follow.
    es.
  - es.
  - rewrite Nat.add_comm.
    st.
    follow.
    es.
  - rewrite Nat.add_comm.
    st.
    follow.
    apply IHHP2.
Qed.

Open Scope nat.

Definition Q1 x s :=
  forall a b,
  a+b=s ->
  2<=a ->
  x+2<=s ->
  b mod 2 = 1 ->
  P (inr (a,b)) (inl (s-x-1,x)).

Ltac ec := econstructor.

Lemma Q1_S x s:
  Q1 x s ->
  x+2<=s ->
  1+s<=x*2 ->
  Q1 x (1+s).
Proof.
  unfold Q1.
  intros I2.
  intros.
  assert (a=2\/3<=a) as [E|E] by lia.
  - subst a.
    ec.
    1: do 2 ec.
    replace (1+s-x-1) with (1+(s-x-1)) by lia.
    ec.
    1: lia.
    apply I2; lia.
  - replace a with (1+(a-1)) by lia.
    eapply P5.
    1: apply I2; lia.
    replace (1+s-x-1) with (1+(s-x-1)) by lia.
    ec.
    1: lia.
    apply I2; lia.
Qed.

Definition Q2 x :=
  P (inr (2,x)) (inl ((x+1)/2,(x+1)/2)) /\
  forall a b,
  a+b=x+2 ->
  2<=a ->
  a<>2 ->
  b mod 2 = 1 ->
  P (inr (a,b)) (inl (1,x)).

Definition Q3 x :=
  P (inr (3,x)) (inr (x+3)) /\
  forall a b,
  a+b=x+3 ->
  2<=a ->
  a<>3 ->
  b mod 2 = 1 ->
  P (inr (a,b)) (inl (2,x)).

Definition Q4 x :=
  P (inr (4,x)) (inl (0,x+3)) /\
  forall a b,
  a+b=x+4 ->
  2<=a ->
  a<>4 ->
  b mod 2 = 1 ->
  P (inr (a,b)) (inl (3,x)).

Lemma Q2_S x:
  10 <= x ->
  x mod 2 = 1 ->
  Q2 x ->
  Q3 x.
Proof.
  unfold Q2,Q3.
  intros Hx Hx0 [I1 I2].
  split.
  1: {
    ec.
    1: apply I1.
    replace (x+3) with (1+(x+2)) by lia.
    ec.
    1: lia.
    rewrite Nat.sub_diag.
    replace ((x+1)/2*2+1) with (x+2) by lia.
    ec.
  }
  intros.
  replace a with (1+(a-1)) by lia.
  assert (a=2\/3<=a) as [E|E] by lia.
  - subst a.
    ec.
    1: do 2 ec.
    ec.
    1: lia.
    apply I2; lia.
  - replace a with (1+(a-1)) by lia.
    eapply P5.
    1: apply I2; lia.
    ec.
    1: lia.
    apply I2; lia.
Qed.

Lemma Q3_S x:
  10<=x ->
  Q3 x ->
  Q4 x.
Proof.
  unfold Q3,Q4.
  intros Hx [I1 I2].
  split.
  1: ec; apply I1.
  intros.
  replace a with (1+(a-1)) by lia.
  assert (a=2\/3<=a) as [E|E] by lia.
  - subst a.
    ec.
    1: do 2 ec.
    ec.
    1: lia.
    apply I2; lia.
  - replace a with (1+(a-1)) by lia.
    eapply P5.
    1: apply I2; lia.
    ec.
    1: lia.
    apply I2; lia.
Qed.

Lemma Q4_S x:
  10<=x ->
  Q4 x ->
  Q1 x (x+5).
Proof.
  unfold Q1,Q4.
  intros Hx [I1 I2].
  intros.
  replace a with (1+(a-1)) by lia.
  assert (a=2\/3<=a) as [E|E] by lia.
  - subst a.
    ec.
    1: do 2 ec.
    replace (x+5-x-1) with 4 by lia.
    ec.
    1: lia.
    apply I2; try lia.
  - destruct (Nat.eqb_spec a 5) as [E0|E0].
    + subst a.
      replace b with x by lia.
      eapply P5.
      1: apply I1.
      replace (x+5-x-1) with 4 by lia.
      ec.
      1: lia.
      apply I2; lia.
    + eapply P5.
      1: apply I2; lia.
      replace (x+5-x-1) with 4 by lia.
      ec.
      1: lia.
      apply I2; lia.
Qed.

Ltac flia := repeat (lia||f_equal).

Lemma Q1_S' x:
  10<=x ->
  Q1 x (x*2) ->
  Q2 (x*2-1).
Proof.
  unfold Q1,Q2.
  intros Hx I2.
  split.
  1:{
    replace ((x*2-1+1)/2) with (1+(x-1)) by lia.
    ec.
    1: do 2 ec.
    ec.
    1: lia.
    applys_eq I2; flia.
  }
  intros.
  replace a with (1+(a-1)) by lia.
  assert (a=2\/3<=a) as [E|E] by lia.
  - subst a.
    ec.
    1: do 2 ec.
    ec.
    1: lia.
    applys_eq I2; flia.
  - replace a with (1+(a-1)) by lia.
    eapply P5.
    1: apply I2; lia.
    ec.
    1: lia.
    replace (x-(x*2-x-1)) with 1 by lia.
    ec.
    applys_eq P3; flia.
Qed.

Definition Q0 x :=
  Q2 x /\ Q3 x /\ Q4 x /\
  (forall s, x+5<=s<=x*2 -> Q1 x s).

Lemma Q2_Q0 x:
  10<=x ->
  x mod 2 = 1 ->
  Q2 x ->
  Q0 x.
Proof.
  unfold Q0.
  intros Hx Hx0 HQ2.
  split.
  1: apply HQ2.
  epose proof HQ2 as HQ3.
  apply Q2_S in HQ3.
  2,3: lia.
  split.
  1: apply HQ3.
  epose proof HQ3 as HQ4.
  apply Q3_S in HQ4.
  2: lia.
  split.
  1: apply HQ4.
  intro s.
  induction s.
  1: lia.
  intros.
  assert (s=x+4\/x+5<=s) as [E|E] by lia.
  - subst s.
    applys_eq Q4_S; try assumption; flia.
  - apply Q1_S.
    2,3: lia.
    apply IHs; lia.
Qed.

Lemma Q0_S x:
  10<=x ->
  x mod 2 = 1 ->
  Q0 x ->
  Q0 (x*2-1).
Proof.
  intros Hx Hx0 HQ0.
  apply Q2_Q0.
  1,2: lia.
  apply Q1_S'.
  1: lia.
  apply HQ0; lia.
Qed.

Ltac solve_v1 :=
  solve[cbn; ec; solve_v1].

Ltac invs :=
  match goal with
  | [H: _ + _ = _ |- _] => inverts H
  end;
  try lia;
  clear;
  try solve_v1.

Lemma Q1_O:
  Q1 10 13.
Proof.
  unfold Q1.
  intros.
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  destruct a; [invs |].
  lia.
Time Qed.

Lemma Q0_O:
  Q0 19.
Proof.
  apply Q2_Q0.
  1,2: lia.
  apply (Q1_S' 10); try lia.
  do 7 (apply Q1_S; try lia; cbn).
  apply Q1_O.
Qed.

Lemma Q0_n i:
  Q0 (2^i*18+1).
Proof.
  induction i.
  1: apply Q0_O.
  cbn[Nat.pow].
  apply Q0_S in IHi; try lia.
  applys_eq IHi; flia.
Qed.

Lemma pow2_ge i:
  2^i>=i+1.
Proof.
  induction i; cbn[Nat.pow]; lia.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply sigma_score_unbounded_nonhalt.
  intros n.
  epose proof (Q0_n n) as [_ [_ [_ I1]]].
  unshelve epose proof (I1 (2^n*18+6) _ (2^n*18+5) 1 _ _ _ _) as I1; try lia.
  eapply (P_spec) in I1.
  rewrite lpow_all0 in I1 by solve_const0_eq.
  eexists _,_; split.
  - eapply evstep_trans.
    2: apply I1.
    es.
  - epose proof (pow2_ge n).
    split.
    1: solve_sigma_score.
    lia.
Qed.

End TM1.

