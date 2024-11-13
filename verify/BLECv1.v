From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter.
From BusyCoq Require Import BinaryCounterFull.

Open Scope list.

Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC0RB_0LE1LD_1RB0LD_0RF---_1RF1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{D}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{D}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition d0 := [1;1;0;0;0;0].
Definition d1 := [1;1;0;1;1;0].
Definition d2 := [1;1;1;0;1;0].
Definition f0 := [1;1;0;0].
Definition f0' := [1;1;1;0].
Definition dh := [1;1;0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RD_0LA1LA_---1RE_1RF1LB_0RC0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM2.

Module TM3.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC0RE_0RB1LD_1RB0LD_---1RF_1RA1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{D}} [1;1] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1;0] {{F}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{D}} [1;1] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1;0] {{F}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [1;1;1;0].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM3.

Module TM4.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC1RD_---1LA_1RF1LE_1LC0RB_1RE0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{D}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM4.

Module TM5.

Definition tm := Eval compute in (TM_from_str "1RB0LC_1LC0RE_---1LD_1RB0LD_---1RF_1RA1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{D}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{F}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{D}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{F}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM5.

Module TM6.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA0RD_1RB0LC_---1RE_1RF1LB_1RB0LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM6.

Module TM7.

Definition tm := Eval compute in (TM_from_str "1LB0RD_0RC1LC_1RA0LC_---1RE_1RF1LA_1RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM7.

Module TM8.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC1LC_1RA0LC_---1RE_1RF1LA_1RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM8.

Module TM9.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LC_1RA0LC_---1RE_1RF1LA_1RA0LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{C}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM9.

Module TM10.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1LC1LF_1RA0LB_---1RE_1RC1LA_1RA0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{F}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{F}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{E}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM10.

Module TM11.

Definition tm := Eval compute in (TM_from_str "1LB0RE_0RC1LD_1RA0LB_1RA0LD_---1RF_1RC1LA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{D}} [0] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [1] {{F}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [0;1] ([0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{D}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [1] {{F}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [0;1;1;1].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM11.

Module TM12.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LA_1RD0RC_1RE0LB_1LB0RF_---1LB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [1;1;1;0].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM12.

Module TM13.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1RC1LA_1RD0RC_1RE0LB_0RF1RC_0LA---").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [1;1;1;0].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM13.

Module TM14.

Definition tm := Eval compute in (TM_from_str "1LB1RC_1RC1LF_---0RD_1RE0RD_1RA0LB_1LB0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [0] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [0] {{D}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [1;1;1;0].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM14.

Module TM15.

Definition tm := Eval compute in (TM_from_str "1LB1RF_1RC1LE_1RD0RC_1RA0LB_1LB0LE_---0RC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{B}} [1] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [0] {{C}}> r) (at level 30).

Definition d0 := [0;0;0;0;1;1].
Definition d1 := [0;1;1;0;1;1].
Definition d2 := [1;0;1;0;1;1].
Definition f0 := [0;0;1;1].
Definition f0' := [1;1;1;0].
Definition dh := [0;1;1;0; 1;1;1;0;1] *> const 0.
Definition mr:list Sym := [].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM15.

Module TM16.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC0RF_1RD1LA_1RE0RD_1RB0LC_---1LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [0;0;1] ([0;0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition d0 := [1;1;1;0;0;0;0].
Definition d1 := [1;1;1;0;1;1;0].
Definition d2 := [1;1;1;1;0;1;0].
Definition f0 := [1;1;1;0;0].
Definition f0' := [1;1;0;0;1].
Definition dh := [1;1;1;0;1;1;0; 1;1;1;1;0;1] *> const 0.
Definition mr:list Sym := [0;0].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~0) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+7))~0)%positive by lia.
  unfold_seg.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (2+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+2))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 10)))) with ((Pos.of_nat (m*3+8))~0)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+2)) as [I1 I2].
  replace ((m*2+1)*2+2) with ((m*2+2)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+12)) (2+m) (m*2+3)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM16.

Module TM17.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC---_1RD1LA_1RE0RD_1RF0LC_1LC1RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [0;0;1] ([0;0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{F}}> r) (at level 30).

Definition d0 := [1;1;1;0;0;0;0].
Definition d1 := [1;1;1;0;1;1;0].
Definition d2 := [1;1;1;1;0;1;0].
Definition f0 := [1;1;1;0;0].
Definition f0' := [1;1;0;0;1].
Definition dh := [1;1;1;0;1;1;0; 1;1;1;1;0;1] *> const 0.
Definition mr:list Sym := [0;0].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~0) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+7))~0)%positive by lia.
  unfold_seg.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (2+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+2))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 10)))) with ((Pos.of_nat (m*3+8))~0)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+2)) as [I1 I2].
  replace ((m*2+1)*2+2) with ((m*2+2)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+12)) (2+m) (m*2+3)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM17.

Module TM18.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC1RD_1RD1LA_---0RE_1RF0RE_1RB0LC").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [0;0;1] ([0;0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition d0 := [1;1;1;0;0;0;0].
Definition d1 := [1;1;1;0;1;1;0].
Definition d2 := [1;1;1;1;0;1;0].
Definition f0 := [1;1;1;0;0].
Definition f0' := [1;1;0;0;1].
Definition dh := [1;1;1;0;1;1;0; 1;1;1;1;0;1] *> const 0.
Definition mr:list Sym := [0;0].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~0) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+7))~0)%positive by lia.
  unfold_seg.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (2+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+2))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 10)))) with ((Pos.of_nat (m*3+8))~0)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+2)) as [I1 I2].
  replace ((m*2+1)*2+2) with ((m*2+2)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+12)) (2+m) (m*2+3)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM18.

Module TM19.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC1RF_1RD1LA_1RE0RD_1RB0LC_---0RD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{D}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0] [0;0;1] ([0;0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition d0 := [1;1;1;0;0;0;0].
Definition d1 := [1;1;1;0;1;1;0].
Definition d2 := [1;1;1;1;0;1;0].
Definition f0 := [1;1;1;0;0].
Definition f0' := [1;1;0;0;1].
Definition dh := [1;1;1;0;1;1;0; 1;1;1;1;0;1] *> const 0.
Definition mr:list Sym := [0;0].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~0) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+7))~0)%positive by lia.
  unfold_seg.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (2+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+2))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 10)))) with ((Pos.of_nat (m*3+8))~0)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+2)) as [I1 I2].
  replace ((m*2+1)*2+2) with ((m*2+2)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+12)) (2+m) (m*2+3)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM19.

Module TM20.

Definition tm := Eval compute in (TM_from_str "1LB0LA_1LC---_1LD1RE_1RE1LA_1RF0RE_1RC0LD").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{E}}> r) (at level 30).

Definition L n := BinaryCounter [0;0;0;0] [0;0;0;1] ([0;0;0;1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [] {{C}}> r) (at level 30).

Definition d0 := [1;1;1;1;0;0;0;0].
Definition d1 := [1;1;1;1;0;1;1;0].
Definition d2 := [1;1;1;1;1;0;1;0].
Definition f0 := [1;1;1;1;0;0].
Definition f0' := [1;1;0;0;0;1].
Definition dh := [1;1;1;1;0;1;1;0; 1;1;1;1;1;0;1] *> const 0.
Definition mr:list Sym := [0;0].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~0) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+7))~0)%positive by lia.
  unfold_seg.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (2+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+2))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 10)))) with ((Pos.of_nat (m*3+8))~0)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  exec_LInc.
  es; er.
  pose proof (RInc (m*2+2)) as [I1 I2].
  replace ((m*2+1)*2+2) with ((m*2+2)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+12)) (2+m) (m*2+3)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM20.

Module TM21.

Definition tm := Eval compute in (TM_from_str "1RB0LA_1LC0RB_1RD1LA_1LA1RE_1RF---_0RC0LF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <l| r" :=
  (l <{{A}} [] *> r) (at level 30).

Notation "l |l> r" :=
  (l <* [] {{B}}> r) (at level 30).

Definition L n := BinaryCounter [0;0] [1;0] ([1] *> const 0) n.

Lemma LInc:
  forall r n,
    L n <l| r -->+
    L (Pos.succ n) |l> r.
Proof.
  intros.
  apply LInc'; es.
Qed.

Notation "l <r| r" :=
  (l <{{A}} [0] *> r) (at level 30).

Notation "l |r> r" :=
  (l <* [0] {{B}}> r) (at level 30).

Definition d0 := [0;0;0;0;0;0;1;1].
Definition d1 := [0;0;1;1;1;0;1;1].
Definition d2 := [1;0;0;1;1;0;1;1].
Definition f0 := [0;0;0;1;1].
Definition f0' := [0;1;1;1;1].
Definition dh := [0;0;1;1;1;0;1;1;1;0;0;1;1] *> const 0.
Definition mr:list Sym := [1;1].

Inductive R: nat -> side -> Prop :=
  | R0: R 0 (d0 *> dh)
  | R1: R 1 (d1 *> dh)
  | R2: R 2 (f0 *> d2 *> dh)
  | R00 x y: R (x*4) y -> R (x*6+3) (f0^^(x) *> d0 *> y)
  | R10 x y: R (x*4) y -> R (x*6+4) (f0^^(1+x) *> d1 *> y)
  | R20 x y: R (x*4) y -> R (x*6+5) (f0^^(1+x) *> d2 *> y)
  | R01 x y: R (x*4+2) y -> R (x*6+6) (f0^^(1+x) *> d0 *> y)
  | R11 x y: R (x*4+2) y -> R (x*6+7) (f0^^(1+x) *> d1 *> y)
  | R21 x y: R (x*4+2) y -> R (x*6+8) (f0^^(2+x) *> d2 *> y)
.

Lemma R_unique x y y0:
  R x y ->
  R x y0 ->
  y=y0.
Proof.
  gen y y0.
  induction x using strong_induction.
  intros.
  inverts H0; inverts H1; try lia; try congruence.
  all: assert(x=x0) by lia; subst x0; repeat f_equal.
  1,2,3: eapply (H (x*4)); eauto; lia.
  1,2,3: eapply (H (x*4+2)); eauto; lia.
Qed.

Lemma R_exist x:
  { y | R x y }.
Proof.
  induction x using lt_wf_rec.
  pose proof (Nat.div_mod_eq x 6) as Hx.
  remember (x/6) as x1.
  remember (x mod 6) as x2.
  epose proof (Nat.mod_upper_bound x 6 _) as Hx2u.
  destruct x2 as [|[|[|[|[|[|]]]]]].
  7: lia.
  clear Heqx1 Heqx2.
  subst x.
  - destruct x1 as [|x1].
    + eexists. apply R0.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R01 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R1. lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R11 _ _ H0). lia.
  - destruct x1 as [|x1].
    + eexists. applys_eq R2; lia.
    + epose proof (H (x1*4+2) _) as [y H0].
      eexists.
      applys_eq (R21 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R00 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R10 _ _ H0). lia.
  - epose proof (H (x1*4) _) as [y H0].
    eexists.
    applys_eq (R20 _ _ H0). lia.
Unshelve.
  all: lia.
Defined.

Definition Rc x := let (y,_):=R_exist x in y.
Lemma Rc_spec x: R x (Rc x).
Proof.
  unfold Rc.
  destruct (R_exist x); tauto.
Qed.
Lemma R_spec x y: R x y -> y = Rc x.
Proof.
  intros H.
  eapply (R_unique x); eauto.
  apply Rc_spec.
Qed.

Ltac unfold_seg := unfold f0,f0',d0,d1,d2,dh,mr.

Lemma RInc:
  forall n,
    (forall l,
    l |r> Rc (n*2) -->+ l <r| Rc (n*2+1)) /\
    (forall l,
    l <* f0' |r> Rc (n*2+1) -->+ l <r| Rc (n*2+2)
    ).
Proof.
  unfold_seg.
  intros.
  induction n using strong_induction.
  intros.
  split; intros.
  {
    unfold Rc.
    destruct (R_exist (n*2)) as [y H0].
    destruct (R_exist (n*2+1)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - assert (x=O) by lia; subst x.
      inverts H2; try lia.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (1+x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2+1) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4+2) with ((x*2+1)*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
  }
  {
    unfold Rc.
    destruct (R_exist (n*2+1)) as [y H0].
    destruct (R_exist (n*2+2)) as [y1 H1].
    inverts H0; inverts H1; try lia.
    - es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      unshelve epose proof (H (x*2) _) as H. 1: lia.
      destruct H as [H H'].
      pose proof (R_spec _ _ H3). subst y0. clear H3.
      pose proof (R_spec _ _ H4). subst y. clear H4.
      es; er.
      replace (x*4) with (x*2*2) by lia.
      follow100 H.
      es; er.
      follow100 H'.
      es; er; finish.
    - unfold_seg.
      assert (x=x0) by lia; subst x0.
      pose proof (R_unique _ _ _ H3 H4); subst y0.
      es.
  }
Qed.


Definition S0 k n m := L k |l> mr *> f0^^n *> d2 *> Rc (m*2).

Ltac exec_LInc := es; er; follow100 LInc.

Lemma Inc k n m:
  S0 k (1+n) m -->*
  S0 (k+3)%positive n (1+m).
Proof.
  unfold S0.
  unfold_seg.
  es; er.
  pose proof (RInc m) as [I1 I2].
  follow100 I1.
  es; er.
  follow100 I2.
  do 3 exec_LInc.
  simpl_rotate.
  finish.
Qed.

Lemma Incs k n m:
  S0 k n m -->*
  S0 (Pos.of_nat (n*3+(Pos.to_nat k))) O (n+m).
Proof.
  gen k m.
  ind n Inc.
Qed.

Lemma Rc_0:
  Rc 0 = d0 *> dh.
Proof.
  pose proof (Rc_spec 0) as H.
  inverts H; try lia.
  reflexivity.
Qed.

Lemma Rc_4 x:
  Rc (x*6+4) = f0^^(1+x) *> d1 *> Rc (x*4).
Proof.
  pose proof (Rc_spec (x*6+4)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_6 x:
  Rc (x*6+6) = f0^^(1+x) *> d0 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+6)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Lemma Rc_8 x:
  Rc (x*6+8) = f0^^(2+x) *> d2 *> Rc (x*4+2).
Proof.
  pose proof (Rc_spec (x*6+8)) as H.
  inverts H; try lia.
  assert (x=x0) by lia; subst x0.
  unfold_seg.
  simpl_rotate.
  repeat f_equal.
  apply R_spec; auto.
Qed.

Definition config m :=
  S0 ((Pos.of_nat (m*3+6))~1) O (m*3+2).

Lemma init:
  c0 -->*
  config O.
Proof.
  unfold config,S0. cbn.
  replace 4 with (O*6+4) by lia.
  rewrite (Rc_4 O). cbn.
  rewrite Rc_0. cbn.
  solve_init.
Qed.

Lemma BigStep m:
  config m -->+
  config (m+1).
Proof.
  remember (config (m+1)) as tg.
  unfold config.
  unfold S0.
  replace ((m*3+2)*2) with (m*6+4) by lia.
  rewrite Rc_4.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2)) as [I1 I2].
  replace (m*4) with (m*2*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 3 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+9)) (2+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((2+m+(m*2+1))*2) with (m*6+6) by lia.
  rewrite Rc_6.
  replace (Pos.of_nat ((2 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 9)))) with ((Pos.of_nat (m*3+7))~1)%positive by lia.
  unfold_seg.
  es; er.
  exec_LInc.
  mid (S0 (Pos.of_nat (m*3+8)) (3+m) (m*2+1)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  unfold S0.
  replace ((3+m+(m*2+1))*2) with (m*6+8) by lia.
  rewrite Rc_8.
  replace (Pos.of_nat ((3 + m) * 3 + Pos.to_nat (Pos.of_nat (m * 3 + 8)))) with ((Pos.of_nat (m*3+8))~1)%positive by lia.
  unfold_seg.
  es; er.
  pose proof (RInc (m*2+1)) as [I1 I2].
  replace (m*4+2) with ((m*2+1)*2) by lia.
  follow100 I1.
  es; er.
  follow100 I2.
  clear I1 I2.
  do 2 exec_LInc.
  mid (S0 (Pos.of_nat (m*3+10)) (3+m) (m*2+2)).
  1: unfold S0; unfold_seg; simpl_rotate; finish.
  follow Incs.

  subst tg.
  unfold config.
  finish.
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt.
  1: apply init.
  eapply progress_nonhalt_simple.
  intros m; exists (m+1).
  apply BigStep.
Qed.

End TM21.

