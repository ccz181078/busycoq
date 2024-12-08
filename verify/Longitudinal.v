From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list.

Definition DH0:Type := Q*(list Sym).
Definition DH:Type := Q*(list Sym)*dir.

Definition to_DH_config(l r:side)(x:DH) :=
let '(QX,qX,d):=x in
match d with
| R => l <* qX {{QX}}> r
| L => l <{{QX}} qX *> r
end.

Notation "l {{{ x }}} r" := (to_DH_config l r x) (at level 30, only parsing).

Definition sideRL(tm:TM)(h1 h2:DH0)(r1 r2:side):Prop :=
forall l,
l {{{ (h1,R) }}} r1 -[ tm ]->+
l {{{ (h2,L) }}} r2.

Definition sideLR(tm:TM)(h1 h2:DH0)(l1 l2:side):Prop :=
forall r,
l1 {{{ (h1,L) }}} r -[ tm ]->+
l2 {{{ (h2,R) }}} r.

Definition segRR(tm:TM)(h1 h2:DH0)(w1 w2:list Sym):Prop :=
forall l r,
l {{{ (h1,R) }}} w1 *> r -[ tm ]->*
l <* w2 {{{ (h2,R) }}} r.

Definition segLL(tm:TM)(h1 h2:DH0)(w1 w2:list Sym):Prop :=
forall l r,
l <* w1 {{{ (h1,L) }}} r -[ tm ]->*
l {{{ (h2,L) }}} w2 *> r.

Definition segRL(tm:TM)(h1 h2:DH0)(w1 w2:list Sym):Prop :=
forall l r,
l {{{ (h1,R) }}} w1 *> r -[ tm ]->+
l {{{ (h2,L) }}} w2 *> r.

Definition segLR(tm:TM)(h1 h2:DH0)(w1 w2:list Sym):Prop :=
forall l r,
l <* w1 {{{ (h1,L) }}} r -[ tm ]->+
l <* w2 {{{ (h2,R) }}} r.

Inductive sideRLs(tm:TM): list (DH0*DH0) -> side -> side -> Prop :=
| sideRLseq_O r: sideRLs tm nil r r
| sideRLseq_S h1 h2 r1 r2 r3 ls:
    sideRL tm h1 h2 r1 r2 ->
    sideRLs tm ls r2 r3 ->
    sideRLs tm ((h1,h2)::ls) r1 r3.

Lemma sideRLs_trans {tm ls1 ls2 r1 r2 r3}:
  sideRLs tm ls1 r1 r2 ->
  sideRLs tm ls2 r2 r3 ->
  sideRLs tm (ls1++ls2) r1 r3.
Proof.
  intros H1 H2.
  induction H1.
  1: apply H2.
  econstructor; eauto.
Qed.

Lemma sideRLs_split {tm ls1 ls2 r1 r2}:
  sideRLs tm (ls1++ls2) r1 r2 ->
  exists r3,
  sideRLs tm ls1 r1 r3 /\
  sideRLs tm ls2 r3 r2.
Proof.
  gen ls2 r1 r2.
  induction ls1; introv H.
  - exists r1.
    split; eauto.
    constructor.
  - inverts H.
    destruct (IHls1 _ _ _ H5) as [r4 [H1' H2']].
    exists r4; split; auto.
    econstructor; eauto.
Qed.

Fixpoint lrcons(l:DH0)(ls:list (DH0*DH0))(r:DH0):list (DH0*DH0) :=
match ls with
| nil => (l,r)::nil
| (a,b)::t => (l,a)::(lrcons b t r)
end.

Lemma lrcons_lrcons h1 h2 ls h3 h4:
  lrcons h1 (lrcons h2 ls h3) h4 =
  (h1,h2)::ls++[(h3,h4)].
Proof.
  gen h1 h2 h3 h4.
  induction ls as [|[a b] t]; cbn; intros.
  1: reflexivity.
  rewrite IHt.
  reflexivity.
Qed.

Lemma lrcons_app h1 ls0 h2 h0 ls1 h3:
  (lrcons h1 ls0 h2 ++ lrcons h0 ls1 h3) = (lrcons h1 (ls0++(h2,h0)::ls1) h3).
Proof.
  gen h1.
  induction ls0 as [|[a b] t]; intros; cbn.
  1: reflexivity.
  rewrite IHt.
  reflexivity.
Qed.

Inductive segLRs: TM -> (list (DH0*DH0)) -> (list Sym) -> (list Sym) -> Prop :=
| segLRs_O tm w1: segLRs tm [] w1 w1
| segLRs_S tm h1 h2 ls1 w1 w2 w3:
  segLR tm h1 h2 w1 w2 ->
  segLRs tm ls1 w2 w3 ->
  segLRs tm ((h1,h2)::ls1) w1 w3
.

Inductive segRLs: TM -> (list (DH0*DH0)) -> (list (DH0*DH0)) -> (list Sym) -> (list Sym) -> Prop :=
| segRLs_O tm w1: segRLs tm [] [] w1 w1
| segRLs_S tm h1 h2 ls1 ls2 w1 w2 w3:
  segRL tm h1 h2 w1 w2 ->
  segRLs tm ls1 ls2 w2 w3 ->
  segRLs tm ((h1,h2)::ls1) ls2 w1 w3
| segRLs_lrcons tm ls2 ls3 ls4 w1 w2 w3 w4 w5 h1 h2 h3 h4:
  segRR tm h1 h3 w1 w3 ->
  segLL tm h4 h2 w4 w5 ->
  segLRs tm ls2 w3 w4 ->
  segRLs tm ls3 ls4 w5 w2 ->
  segRLs tm ((h1,h2)::ls3) ((lrcons h3 ls2 h4)++ls4) w1 w2
.

Lemma segRLs_trans {tm ls1 ls2 ls3 ls4 w1 w2 w3}:
  segRLs tm ls1 ls2 w1 w2 ->
  segRLs tm ls3 ls4 w2 w3 ->
  segRLs tm (ls1++ls3) (ls2++ls4) w1 w3.
Proof.
  intros H.
  gen ls3 ls4 w3.
  induction H.
  - introv H'.
    apply H'.
  - introv H'.
    cbn.
    eapply segRLs_S; eauto.
  - introv H'.
    repeat rewrite <-app_assoc.
    cbn.
    eapply segRLs_lrcons; eauto.
Qed.

Lemma segRLs_split {tm ls1 ls2 ls3 w1 w2}:
  segRLs tm (ls1++ls2) ls3 w1 w2 ->
  exists ls4 ls5 w3,
  segRLs tm ls1 ls4 w1 w3 /\
  segRLs tm ls2 ls5 w3 w2 /\
  ls3 = ls4 ++ ls5.
Proof.
  intros H.
  gen w1 ls3.
  induction ls1; intros w1 ls3.
  - eexists [], _, _.
    repeat split.
    1: constructor.
    apply H.
  - intros H.
    cbn in H.
    inverts H.
    + destruct (IHls1 _ _ H7) as [ls4' [ls5' [w3' [H1' [H2' H3']]]]].
      eexists _,_,_.
      split; [|split]; eauto.
      eapply segRLs_S; eauto.
    + destruct (IHls1 _ _ H9) as [ls4' [ls5' [w3' [H1' [H2' H3']]]]].
      eexists _,_,_.
      split; [|split]; eauto.
      1: eapply segRLs_lrcons; eauto.
      rewrite <-app_assoc.
      congruence.
Qed.

Lemma segLRs_app {tm ls w1 w2 w3}:
  segLRs tm ls w1 w2 ->
  segLRs tm ls (w1++w3) (w2++w3).
Proof.
  intro H.
  induction H.
  1: constructor.
  econstructor; eauto.
  intros l r.
  repeat rewrite Str_app_assoc.
  apply H.
Qed.

Lemma segLRs_trans {tm ls1 ls2 w1 w2 w3}:
  segLRs tm ls1 w1 w2 ->
  segLRs tm ls2 w2 w3 ->
  segLRs tm (ls1++ls2) w1 w3.
Proof.
  intros H.
  induction H; intros.
  1: apply H.
  econstructor; eauto.
Qed.

Lemma segRLs_concat_aux' {tm h2 h3 h4 w2 w3 w4 w5 w6 ls1 ls2}:
  segLL tm h4 h2 w4 w2 ->
  segLRs tm ls1 w3 w4 ->
  segRLs tm (lrcons h3 ls1 h4) ls2 w5 w6 ->
  (
  ((forall l r, l <* w3 {{{ (h3,R) }}} w5 *> r -[ tm ]->+ l {{{ (h2,L) }}} w2 *> w6 *> r) /\ ls2 = []) \/
  exists h5 h6 w7 w8 ls2',
  (forall l r, l <* w3 {{{ (h3,R) }}} w5 *> r -[ tm ]->* l <* w7 {{{ (h5,R) }}} r) /\
  segLL tm h6 h2 w8 (w2++w6) /\
  segLRs tm ls2' w7 w8 /\
  ls2 = lrcons h5 ls2' h6
  ).
Proof.
  gen h3 w3 w5 w6 ls2.
  induction ls1; intros.
  - inverts H0.
    inverts H1.
    + inverts H9.
      left.
      split; auto.
      intros.
      follow10 H8.
      apply H.
    + inverts H11.
      right.
      eexists h5,h6,(w3++w4),(w7++w4),ls0.
      repeat split.
      4: rewrite app_nil_r; reflexivity.
      * intros.
        rewrite Str_app_assoc.
        apply H4.
      * intros l r.
        repeat rewrite Str_app_assoc.
        follow H6.
        apply H.
      * apply segLRs_app,H10.
  - destruct a as [a b].
    inverts H0.
    inverts H1.
    + epose proof (IHls1 _ _ _ _ _ H H9 H11)
      as [[X1 X2]|[h5' [h6' [w7' [w8' [ls2' [X1 [X2 [X3 X4]]]]]]]]].
      * left.
        subst ls2.
        split; auto.
        intros.
        follow11 H10.
        follow11 H8.
        apply X1.
      * right.
        subst ls2.
        eexists h5',h6',_,_,ls2'.
        repeat split.
        -- intros.
           follow100 H10.
           follow100 H8.
           apply X1.
        -- apply X2.
        -- apply X3.
    + epose proof (IHls1 _ _ _ _ _ H H9 H13)
      as [[X1 X2]|[h5' [h6' [w7' [w8' [ls2' [X1 [X2 [X3 X4]]]]]]]]].
      * right.
        subst ls4.
        eexists _,_,_,(w9++w3),_.
        repeat split.
        4: rewrite app_nil_r; reflexivity.
        -- intros.
           follow H4.
           rewrite <-Str_app_assoc.
           finish.
        -- intros l r.
           repeat rewrite Str_app_assoc.
           follow H6.
           follow100 H8.
           follow100 X1.
           finish.
        -- eapply segLRs_app,H12.
      * right.
        subst ls4.
        eexists _,_,_,_,_.
        repeat split.
        4: rewrite lrcons_app; reflexivity.
        -- intros.
           follow H4.
           rewrite <-Str_app_assoc.
           finish.
        -- apply X2.
        -- eapply segLRs_trans.
           1: eapply segLRs_app; eauto.
           econstructor; eauto.
           intros l r.
           repeat rewrite Str_app_assoc.
           follow H6.
           follow10 H8.
           apply X1.
Qed.

Lemma segRLs_concat_aux {tm h1 h2 h3 h4 w1 w2 w3 w4 w5 w6 ls1 ls2}:
  segRR tm h1 h3 w1 w3 ->
  segLL tm h4 h2 w4 w2 ->
  segLRs tm ls1 w3 w4 ->
  segRLs tm (lrcons h3 ls1 h4) ls2 w5 w6 ->
  (
  (segRL tm h1 h2 (w1++w5) (w2++w6) /\ ls2 = []) \/
  exists h5 h6 w7 w8 ls2',
  segRR tm h1 h5 (w1++w5) w7 /\
  segLL tm h6 h2 w8 (w2++w6) /\
  segLRs tm ls2' w7 w8 /\
  ls2 = lrcons h5 ls2' h6
  ).
Proof.
  intros Hr Hl Hlr Hrl.
  epose proof (segRLs_concat_aux' Hl Hlr Hrl)
  as [[X1 X2]|[h5' [h6' [w7' [w8' [ls2' [X1 [X2 [X3 X4]]]]]]]]].
  - left.
    subst ls2.
    split; auto.
    intros l r.
    repeat rewrite Str_app_assoc.
    follow Hr.
    apply X1.
  - right.
    subst ls2.
    eexists _,_,_,_,_.
    repeat split.
    + intros l r.
      rewrite Str_app_assoc.
      follow Hr.
      apply X1.
    + apply X2.
    + apply X3.
Qed.


Lemma segRLs_concat {tm ls1 ls2 ls3 w1 w2 w3 w4}:
  segRLs tm ls1 ls2 w1 w2 ->
  segRLs tm ls2 ls3 w3 w4 ->
  segRLs tm ls1 ls3 (w1++w3) (w2++w4).
Proof.
  intros H.
  gen ls2 ls3 w1 w2 w3 w4.
  induction ls1; introv H1' H2'.
  - inverts H1'.
    inverts H2'.
    constructor.
  - inverts H1'.
    + eapply segRLs_S; eauto.
      intros l r.
      repeat rewrite Str_app_assoc.
      apply H2.
    + epose proof (segRLs_split H2') as [ls5' [ls6' [w7' [H1'' [H2'' H3'']]]]].
      subst ls3.
      specialize (IHls1 _ _ _ _ H8 _ _ H2'').
      epose proof (segRLs_concat_aux H1 H2 H4 H1'') as [[H H']|[h5' [h6' [w7'' [w8'' [ls2' [Hr [Hl [Hlr H']]]]]]]]].
      * eapply segRLs_S.
        1: apply H.
        rewrite H'.
        apply IHls1.
      * rewrite H'.
        eapply segRLs_lrcons; eauto.
Qed.


Lemma sideRLs_segLRs_concat {tm ls h1 h2 w1 w2 r1 r2}:
  segLRs tm ls w1 w2 ->
  sideRLs tm (lrcons h1 ls h2) r1 r2 ->
  forall l,
  l <* w1 {{{ (h1,R) }}} r1 -[ tm ]->+
  l <* w2 {{{ (h2,L) }}} r2.
Proof.
  gen h1 h2 w1 w2 r1 r2.
  induction ls; intros.
  - inverts H.
    cbn in H0.
    inverts H0.
    inverts H6.
    apply H5.
  - destruct a as [a b].
    inverts H.
    inverts H0.
    eapply progress_trans.
    2: apply IHls; eauto.
    follow11 H5.
    apply H7.
Qed.

Lemma segRLs_sideRLs_concat {tm ls1 ls2 w1 w2 r1 r2}:
  segRLs tm ls1 ls2 w1 w2 ->
  sideRLs tm ls2 r1 r2 ->
  sideRLs tm ls1 (w1 *> r1) (w2 *> r2).
Proof.
  intros H.
  gen r1 r2.
  induction H; intros.
  - inverts H.
    constructor.
  - econstructor.
    2: apply IHsegRLs.
    1: intros l; apply H.
    apply H1.
  - epose proof (sideRLs_split H3) as [r3' [H3a H3b]].
    econstructor.
    2: apply IHsegRLs.
    2: apply H3b.
    intros l.
    follow H.
    eapply progress_evstep_trans.
    2: apply H0.
    eapply sideRLs_segLRs_concat; eauto.
Qed.

Lemma to_DH_config_progress_flip {tm h1 h2 d1 d2 l1 l2 r1 r2}:
  l1 {{{ (h1,d1) }}} r1 -[ tm ]->+
  l2 {{{ (h2,d2) }}} r2 ->
  r1 {{{ (h1,flip_dir d1) }}} l1 -[ flip tm ]->+
  r2 {{{ (h2,flip_dir d2) }}} l2.
Proof.
  intros H.
  pose proof (flip_progress _ _ _ H) as H0.
  applys_eq H0.
  all:
  destruct h1 as [h1 h1'];
  destruct h2 as [h2 h2'];
  destruct d1,d2; cbn; try reflexivity.
Qed.

Lemma to_DH_config_progress_unflip {tm h1 h2 d1 d2 l1 l2 r1 r2}:
  l1 {{{ (h1,d1) }}} r1 -[ flip tm ]->+
  l2 {{{ (h2,d2) }}} r2 ->
  r1 {{{ (h1,flip_dir d1) }}} l1 -[ tm ]->+
  r2 {{{ (h2,flip_dir d2) }}} l2.
Proof.
  intros H.
  applys_eq (to_DH_config_progress_flip H).
  rewrite flip_involutive.
  reflexivity.
Qed.

Lemma sideRLs_concat {tm h1 h2 ls l1 l2 r1 r2}:
  sideRLs (flip tm) ls l1 l2 ->
  sideRLs tm (lrcons h1 ls h2) r1 r2 ->
  l1 {{{ (h1,R) }}} r1 -[ tm ]->+
  l2 {{{ (h2,L) }}} r2.
Proof.
  gen h1 h2 l1 l2 r1 r2.
  induction ls; intros.
  - inverts H.
    cbn in H0.
    inverts H0.
    inverts H6.
    apply H5.
  - destruct a as [a b].
    inverts H.
    inverts H0.
    follow11 H5.
    follow11 (to_DH_config_progress_unflip (H6 r4)).
    eapply IHls; eauto.
Qed.

Lemma segRLs_nil {tm ls}:
  segRLs tm ls ls [] [].
Proof.
  induction ls.
  1: constructor.
  destruct a as [a b].
  eapply (segRLs_lrcons) with (ls2:=[]) (w1:=[]) (w2:=[]) (w3:=[]) (w4:=[]) (w5:=[]).
  all: eauto; constructor.
Qed.

Lemma segRLs_wall {tm h1 h2 w w' n}:
  segRR tm h1 h1 w w' ->
  segLL tm h2 h2 w' w ->
  segRLs tm ([(h1,h2)]^^n) ([(h1,h2)]^^n) w w.
Proof.
  induction n; intros.
  1: constructor.
  cbn.
  eapply (segRLs_lrcons) with (ls2:=[]); eauto.
  constructor.
Qed.

Lemma segRLs_wall' {tm h1 h2 h1' h2' w w' n}:
  segRR tm h1 h1' w w' ->
  segLL tm h2' h2 w' w ->
  segRLs tm ([(h1,h2)]^^n) ([(h1',h2')]^^n) w w.
Proof.
  induction n; intros.
  1: constructor.
  cbn.
  eapply (segRLs_lrcons) with (ls2:=[]); eauto.
  constructor.
Qed.

Lemma segRLs_S' {tm h1 h2 h3 h4 ls1 ls2 w1 w2 w3 w4}:
  segRR tm h1 h3 w1 w2 ->
  segLL tm h4 h2 w2 w3 ->
  segRLs tm ls1 ls2 w3 w4 ->
  segRLs tm ((h1,h2)::ls1) ((h3,h4)::ls2) w1 w4.
Proof.
  change ((h3,h4)::ls2) with ((lrcons h3 [] h4)++ls2).
  intros.
  eapply segRLs_lrcons; eauto.
  1: constructor.
Qed.

Module UC1.
Section UnaryCounter1.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w1':list Sym.
Hypothesis Inc:
  segRL tm hR hL w0 w1.
Hypothesis Ov:
  segRR tm hR hR w1 w1'.
Hypothesis Rst:
  segLL tm hL hL w1' w1.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n+m)) ([(hR,hL)]^^m) (w0^^n) (w1^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  - intros l r.
    rewrite Str_app_assoc.
    follow10 Inc.
    rewrite <-Str_app_assoc.
    finish.
  - eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n)) [] (w0^^n) (w1^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter1.
End UC1.

Module BCR.
Section BinaryCounter.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis d0 d1 d1':list Sym.
Hypothesis LR:
  segLR tm hL hR d0 d1.
Hypothesis Carry:
  segLL tm hL hL d1 d1'.
Hypothesis Ret:
  segRR tm hR hR d1' d0.

Lemma Incs n:
  segRLs tm ([(hR,hL)]^^n) ([(hR,hL)]^^(n*2)) d1' d1'.
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  cbn[app].
  replace (S n * 2) with (2+n*2) by lia.
  rewrite lpow_add.
  change ([(hR,hL)]^^2) with (lrcons hR [(hL,hR)] hL).
  eapply segRLs_lrcons; eauto.
  econstructor; eauto.
  econstructor.
Qed.
End BinaryCounter.
End BCR.

Module BC.
Section BinaryCounter.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis d0 d1 d1':list Sym.
Hypothesis RL:
  segRL tm hR hL d0 d1.
Hypothesis Carry:
  segRR tm hR hR d1 d1'.
Hypothesis Ret:
  segLL tm hL hL d1' d0.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*2+1)) ([(hR,hL)]^^n) d0 d1.
Proof.
  induction n.
  1: {
    eapply segRLs_S; eauto.
    econstructor.
  }
  replace (S n * 2 + 1) with (2+(n*2+1)) by lia.
  cbn[lpow].
  rewrite lpow_add.
  eapply segRLs_trans.
  2: apply IHn.
  eapply segRLs_S; eauto.
  cbn.
  eapply segRLs_S'; eauto.
  econstructor.
Qed.

Lemma Mul2 n:
  segRLs tm ([(hR,hL)]^^(n*2)) ([(hR,hL)]^^n) d1 d1.
Proof.
  induction n.
  1: constructor.
  cbn.
  eapply segRLs_S'; eauto.
  eapply segRLs_S; eauto.
Qed.

Lemma Incs n:
  segRLs tm ([(hR,hL)]^^((2^n)-1)) [] (d0^^n) (d1^^n).
Proof.
  induction n.
  1: constructor.
  cbn[lpow].
  cbn[Nat.pow].
  epose proof (Nat.pow_nonzero 2 n).
  replace (2*2^n-1) with ((2^n-1)*2+1) by lia.
  eapply segRLs_concat.
  1: apply Incs'.
  apply IHn.
Qed.

Lemma IncsMul2 n:
  segRLs tm ([(hR,hL)]^^((2^n*2)-2)) [] (d1 ++ d0^^n) (d1 ++ d1^^n).
Proof.
  replace (2^n*2-2) with ((2^n-1)*2) by lia.
  eapply segRLs_concat.
  1: apply Mul2.
  apply Incs.
Qed.
End BinaryCounter.
End BC.

Ltac solve_LOverflow :=
  intros;
  simpl_tape; cbn; step1s;
  use_shift_rule; cbn;
  step1s;
  use_shift_rule; cbn;
  simpl_rotate;
  step1s.

Lemma Str_app_assoc_1{A} a (b:A) c:
  a *> [b] *> c =
  (a ++ [b]) *> c.
Proof.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lrcons_lpow1 h1 h2 n:
  n<>O ->
  lrcons h1 ([(h2,h1)]^^(n-1)) h2 = ([(h1,h2)]^^n).
Proof.
  intros H.
  destruct n.
  1: lia.
  replace (S n - 1) with n by lia.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn. 2: lia.
  reflexivity.
Qed.


Module UC2.
Section UnaryCounter2.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w2 w2':list Sym.
Hypothesis Inc0:
  segRL tm hR hL w0 w1.
Hypothesis Inc1:
  segRL tm hR hL w1 w2.
Hypothesis Ov:
  segRR tm hR hR w2 w2'.
Hypothesis Rst:
  segLL tm hL hL w2' w2.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n*2+m)) ([(hR,hL)]^^m) (w0^^n) (w2^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc0.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc1.
    rewrite <-Str_app_assoc.
    finish.
  }
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*2)) [] (w0^^n) (w2^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter2.
End UC2.


Module UC3.
Section UnaryCounter3.
Hypothesis tm:TM.
Hypothesis hR hL:DH0.
Hypothesis w0 w1 w2 w3 w3':list Sym.
Hypothesis Inc0:
  segRL tm hR hL w0 w1.
Hypothesis Inc1:
  segRL tm hR hL w1 w2.
Hypothesis Inc2:
  segRL tm hR hL w2 w3.
Hypothesis Ov:
  segRR tm hR hR w3 w3'.
Hypothesis Rst:
  segLL tm hL hL w3' w3.

Lemma Incs n m:
  segRLs tm ([(hR,hL)]^^(n*3+m)) ([(hR,hL)]^^m) (w0^^n) (w3^^n).
Proof.
  induction n.
  1: apply segRLs_nil.
  cbn.
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc0.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc1.
    rewrite <-Str_app_assoc.
    finish.
  }
  eapply segRLs_S.
  1:{
    intros l r.
    rewrite Str_app_assoc.
    follow10 Inc2.
    rewrite <-Str_app_assoc.
    finish.
  }
    eapply segRLs_concat.
    2: apply IHn.
    eapply segRLs_wall; eauto.
Qed.

Lemma Incs' n:
  segRLs tm ([(hR,hL)]^^(n*3)) [] (w0^^n) (w3^^n).
Proof.
  applys_eq (Incs n O).
  f_equal; lia.
Qed.

End UnaryCounter3.
End UC3.

