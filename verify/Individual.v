(** * Utilities for proving individual machines *)

From Coq Require Export Lists.Streams.
From Coq Require Import Lia.
From Coq Require Import PeanoNat.
From BusyCoq Require Export Permute.
From BusyCoq Require Export Enumerate.
Set Default Goal Selector "!".

Module Individual (Ctx : Ctx).
  Module Enumerate := Enumerate Ctx. Export Enumerate.

(** Trivial lemmas, but [simpl] in these situations leaves a mess. *)
Lemma move_left_const : forall s0 s r,
  move_left (const s0 {{s}} r) = const s0 {{s0}} s >> r.
Proof. reflexivity. Qed.

Lemma move_right_const : forall l s s0,
  move_right (l {{s}} const s0) = l << s {{s0}} const s0.
Proof. reflexivity. Qed.

Lemma tl_const : forall A (x : A), tl (const x) = const x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite move_left_const move_right_const tl_const : tape_pre.
#[export] Hint Rewrite <- const_unfold : tape_post.

Lemma lpow_shift' : forall A n (xs : list A) ys,
  xs^^n *> xs *> ys = xs *> xs^^n *> ys.
Proof.
  introv.
  rewrite <- Str_app_assoc.
  rewrite lpow_shift.
  rewrite Str_app_assoc.
  reflexivity.
Qed.

Lemma lpow_S : forall {A} n (xs : list A),
  xs^^(S n) = xs +> xs^^n.
Proof. reflexivity. Qed.

#[export] Hint Rewrite lpow_shift' lpow_add : tape_post.
#[export] Hint Rewrite @Str_app_assoc : tape_post.

(** The direct formulation isn't as useful when the proof that the two
    configurations are the same is non-trivial. *)
Lemma evstep_refl' : forall tm c c',
  c = c' ->
  c -[ tm ]->* c'.
Proof. intros. subst c'. auto. Qed.

(** Solve an equality goal where some subexpressions are equal by [lia],
    in an otherwise [reflexivity]-compatible spine. *)
Ltac lia_refl := solve [repeat (lia || f_equal)].

(** [prove_step] proves a goal of the form [c -[ tm ]-> ?c'], where the value
    returned by [tm] in this situation can be calculated by reflexivity. *)
Ltac prove_step_left := apply @step_left; reflexivity.
Ltac prove_step_right := apply @step_right; reflexivity.
Ltac prove_step := prove_step_left || prove_step_right.

(** Simplify a tape expression, removing [move_left] and [move_right] leftover
    after [prove_step], without needlessly expanding the [cofix] in [const s0]. *)
Ltac simpl_tape :=
  autorewrite with tape_pre;
  simpl;
  autorewrite with tape_post.

(** Prove a goal of the form [c -->+ c'] that consists of a single TM step. *)
Ltac finish_progress := apply progress_base; prove_step.

(** Prove a goal of the form [c -->* c'] that consists of zero TM steps. *)
Ltac finish_evstep := apply evstep_refl'; try (reflexivity || lia_refl).
Ltac finish := finish_evstep || finish_progress.

(** Advance the configuration on the left-hand side of a [-->+] or [-->*]
    by one TM step. *)
Ltac step := (eapply evstep_step || eapply progress_step); [prove_step | simpl_tape].

(** Run [step] until we reach the state that is being asked for, or until the
    TM gets stuck (because the symbolic state doesn't make it clear what symbol
    is under the tape). *)
Ltac execute := introv; repeat (try solve [finish]; step).

(** For a goal of the form [c -->+ c'], take steps until the TM gets stuck,
    taking at least one step. Transforms the goal into [c'' -->* c'] as a result. *)
Ltac start_progress := eapply progress_intro; [prove_step | simpl_tape]; execute.

(** [follow H], on a goal of the form [H: c1 -->* c2  |-  c1' -->* c3], will
    transform it into [|-  c2 -->* c3].  [adjust] is used to make it work when
    the equality [c1 = c1'] isn't as clear.

    [follow], without an argument, will try using the assumptions
    in the context. *)
Ltac do_adjust H ty :=
  lazymatch ty with
  | _ -> ?ty => do_adjust H ty
  | ?c1 -[ _ ]->* _ =>
    lazymatch goal with
    | |- ?c2 -[ _ ]->* _ =>
      replace c2 with c1; [apply H | reflexivity || lia_refl]
    end
  end.

Ltac adjust H := let ty := type of H in do_adjust H ty.
Ltac adjusted H := apply H || adjust H.
Ltac follow_trans :=
  lazymatch goal with
  | |- _ -[ _ ]->* _ => eapply evstep_trans
  | |- _ -[ _ ]->+ _ => eapply evstep_progress_trans
  end.

Ltac follow_hyp H := follow_trans; [adjusted H; eauto |].
Ltac follow_assm :=
  match goal with
  | H: _ |- _ => follow_hyp H
  end.

Tactic Notation "follow" := follow_assm.
Tactic Notation "follow" constr(H) := follow_hyp H.

(** For trivial [-->*] goals, provable by stepping and applying assumptions. *)
Ltac triv := intros; repeat (try solve [finish]; (step || follow)).


Ltac follow10 H :=
  eapply progress_evstep_trans; [ apply H | idtac ].

Ltac follow100 H :=
  apply progress_evstep;
  follow10 H.

Ltac follow11 H :=
  eapply progress_trans; [ apply H | idtac ].

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
l <* w1 {{{ (h1,L) }}} r -[ tm ]->*
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

Fixpoint lcons(l:DH0)(ls:list (DH0*DH0)):(list (DH0*DH0))*DH0 :=
match ls with
| nil => (nil,l)
| (a,b)::t => let (x,y):=(lcons b t) in ((l,a)::x,y)
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
        follow H8.
        apply X1.
      * right.
        subst ls2.
        eexists h5',h6',_,_,ls2'.
        repeat split.
        -- intros.
           follow100 H10.
           follow H8.
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
           follow H8.
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
           follow H8.
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
    follow10 H5.
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

Lemma sideRLs_concat_v2 {tm h1 h2 ls ls' l1 l2 r1 r2}:
  lcons h1 ls = (ls',h2) ->
  ls<>[] ->
  sideRLs (flip tm) ls l1 l2 ->
  sideRLs tm ls' r1 r2 ->
  l1 {{{ (h1,R) }}} r1 -[ tm ]->+
  l2 {{{ (h2,R) }}} r2.
Proof.
  gen h1 h2 ls' l1 l2 r1 r2.
  induction ls; intros.
  1: congruence.
  destruct a as [a b].
  cbn in H.
  destruct (lcons b ls) as [ls'0 h2'] eqn:E.
  inverts H.
  inverts H1.
  inverts H2.
  destruct ls as [|h t].
  - cbn in E.
    inverts E.
    inverts H8.
    inverts H9.
    follow11 H6.
    eapply (to_DH_config_progress_unflip (H7 _)).
  - epose proof (IHls _ _ _ _ _ _ _ E _ H8 H9) as I1.
    follow11 H6.
    eapply progress_trans.
    2: apply I1.
    eapply (to_DH_config_progress_unflip (H7 _)).
  Unshelve.
  congruence.
Qed.

Lemma sideRL_1 tm h1 h2 r1 r2:
  sideRL tm h1 h2 r1 r2 ->
  sideRLs tm [(h1,h2)] r1 r2.
Proof.
  intros H.
  econstructor.
  2: constructor.
  apply H.
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

Lemma segRLs_wall'' {tm h1 h2 w n}:
  segRLs tm h1 h2 w w ->
  segRLs tm (h1^^n) (h2^^n) w w.
Proof.
  induction n; intros.
  1: constructor.
  cbn.
  eapply segRLs_trans; eauto.
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

Lemma segRLs_1_2 {tm h1 h2 h3 h4 h5 h6 w1 w2 w3 w4}:
  segRR tm h1 h3 w1 w3 ->
  segLR tm h5 h6 w3 w4 ->
  segLL tm h4 h2 w4 w2 ->
  segRLs tm ((h1,h2)::nil) ((h3,h5)::(h6,h4)::nil) w1 w2.
Proof.
  intros.
  change ((h3,h5)::(h6,h4)::nil) with ((lrcons h3 [(h5,h6)] h4)++nil).
  eapply segRLs_lrcons; eauto.
  2: constructor.
  econstructor; eauto.
  constructor.
Qed.

Definition rcons(ls:list (DH0*DH0))(r:DH0):DH0*(list (DH0*DH0)) :=
match ls with
| [] => (r,[])
| (a,b)::t => (a,lrcons b t r)
end.

Inductive segLLs: TM -> DH0 -> list (DH0*DH0) -> DH0 -> list (DH0*DH0) -> list Sym -> list Sym -> Prop :=
| segLLs_intro tm ls2 ls3 ls4 ls2' w2 w3 w4 w5 h2 h4 h4':
  segLRs tm ls2 w3 w4 ->
  segLL tm h4 h2 w4 w5 ->
  segRLs tm ls3 ls4 w5 w2 ->
  rcons ls2 h4 = (h4',ls2') ->
  segLLs tm h2 ls3 h4' (ls2'++ls4) w3 w2.

Lemma segRLs_RR_LLs tm ls3 ls4 w1 w2 w3 h1 h2 h3 h4:
  segRR tm h1 h3 w1 w3 ->
  segLLs tm h2 ls3 h4 ls4 w3 w2 ->
  segRLs  tm ((h1,h2)::ls3) ((h3,h4)::ls4) w1 w2.
Proof.
  intros I1 I2.
  inverts I2.
  destruct ls2 as [|[a b] ls2].
  - cbn in H2.
    inverts H2.
    cbn.
    change ((h3,h4)::ls1) with (lrcons h3 [] h4 ++ ls1).
    eapply segRLs_lrcons; eauto.
  - cbn in H2.
    inverts H2.
    change ((h3,h4)::lrcons b ls2 h5++ls1) with (lrcons h3 ((h4,b)::ls2) h5 ++ ls1).
    eapply segRLs_lrcons; eauto.
Qed.

Lemma segLLs_LR_LLs tm ls1 ls2 w1 w2 w3 h1 h2 h3 h4:
  segLR tm h2 h3 w1 w3 ->
  segLLs tm h1 ls1 h4 ls2 w3 w2 ->
  segLLs tm h1 ls1 h2 ((h3,h4)::ls2) w1 w2.
Proof.
  intros I1 I2.
  inverts I2.
  change ((h3,h4)::ls2'++ls4) with (((h3,h4)::ls2')++ls4).
  econstructor; eauto.
  1: econstructor; eauto.
  cbn.
  destruct ls0 as [|[a b] ls0]; cbn in *; inverts H2; trivial.
Qed.

Lemma segLLs_LL_RLs tm ls1 ls2 w1 w2 w3 h1 h2:
  segLL tm h2 h1 w1 w3 ->
  segRLs tm ls1 ls2 w3 w2 ->
  segLLs tm h1 ls1 h2 ls2 w1 w2.
Proof.
  intros I1 I2.
  change ls2 with ([]++ls2).
  econstructor; eauto.
  1: constructor.
  trivial.
Qed.

Local Ltac unfold_segXX :=
  unfold segRR,segRL,segLL,segLR in *;
  cbn in *;
  intros;
  simpl_tape.

Lemma evstep_segRLs_trans tm hR hR' hL ls1 ls2 w1 w1' w2:
  (forall l r,
  l {{{ (hR,R) }}} w1 *> r -[ tm ]->*
  l {{{ (hR',R) }}} w1' *> r) ->
  segRLs tm ((hR',hL)::ls1) ls2 w1' w2 ->
  segRLs tm ((hR,hL)::ls1) ls2 w1 w2.
Proof.
  intros I1 I2.
  inverts I2.
  - eapply segRLs_S.
    2: eassumption.
    unfold_segXX.
    follow I1.
    follow10 H6.
    finish.
  - eapply segRLs_lrcons.
    2,3,4: eassumption.
    unfold_segXX.
    follow I1.
    follow H2.
    finish.
Qed.

Lemma segRLs_trans_1 tm QR qR QL qL hL m0 w0 w1 w2 w3 ls1 ls2:
  segRLs tm [((QR,qR),(QL,qL))] ls1 w1 w2 ->
  segRLs tm [((QL,w0),hL)] ls2 (m0::qL++w2) w3 ->
  segRLs tm [((QR,qR++m0::w0),hL)] (ls1++ls2) w1 w3.
Proof.
  intros I1 I2.
  inverts I1.
  - inverts H7.
    inverts I2.
    + inverts H8.
      eapply segRLs_S.
      2: constructor.
      destruct hL as [QL' qL'].
      unfold_segXX.
      follow11 H6.
      specialize (H7 l r).
      rewrite Str_app_assoc in H7.
      apply H7.
    + inverts H10.
      eapply segRLs_lrcons.
      4: constructor.
      * unfold_segXX.
        follow100 H6.
        specialize (H2 l r).
        rewrite Str_app_assoc in H2.
        apply H2.
      * eassumption.
      * eassumption.
  - inverts H9.
    inverts I2.
    + inverts H10.
      rewrite app_nil_r.
      destruct h3 as [Q3 q3].
      destruct h4 as [Q4 q4].
      destruct hL as [Q5 q5].
      eapply segRLs_lrcons.
      4: constructor.
      1: {
        unfold_segXX.
        follow H2.
        rewrite <-(Str_app_assoc w6).
        finish.
      }
      2: eapply segLRs_app; eassumption.
      1: {
        unfold_segXX.
        follow H4.
        specialize (H9 l r).
        rewrite Str_app_assoc in H9.
        follow100 H9.
        finish.
      }
    + inverts H12.
      rewrite app_nil_r.
      rewrite app_assoc.
      rewrite lrcons_app.
      destruct h0 as [Q0 q0].
      destruct h3 as [Q3 q3].
      destruct h4 as [Q4 q4].
      destruct h5 as [Q5 q5].
      destruct hL as [Q6 q6].
      eapply segRLs_lrcons.
      4: constructor.
      * unfold_segXX.
        follow H2.
        rewrite <-(Str_app_assoc w6).
        finish.
      * eassumption.
      * eapply segLRs_trans.
        1: eapply segLRs_app; eassumption.
        eapply segLRs_S.
        2: eassumption.
        unfold_segXX.
        follow H4.
        specialize (H3 l r).
        rewrite Str_app_assoc in H3.
        apply H3.
Qed.

Lemma segRLs_addmul tm a x b c h w1 w2:
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^(x+c)) w1 w2.
Proof.
  intros.
  rewrite (Nat.add_comm _ b).
  rewrite (Nat.add_comm _ c).
  do 2 rewrite lpow_add.
  eapply segRLs_trans.
  1: apply H.
  induction x; cbn[Nat.mul].
  - cbn.
    constructor.
  - cbn[lpow].
    rewrite lpow_add.
    eapply segRLs_trans.
    2: apply IHx.
    apply H0.
Qed.

Lemma segRLs_addmul' tm a x b c h w1 w2:
  x>=c ->
  segRLs tm (h^^b) (h^^c) w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^((x-c)*a+b)) (h^^x) w1 w2.
Proof.
  intros H.
  replace (h^^x) with (h^^(x-c+c)) by (f_equal; lia).
  apply segRLs_addmul.
Qed.

Lemma segRLs_addmul'' tm a x b h w1 w2:
  segRLs tm (h^^b) [] w1 w2 ->
  segRLs tm (h^^a) h w2 w2 ->
  segRLs tm (h^^(x*a+b)) (h^^x) w1 w2.
Proof.
  epose proof (segRLs_addmul tm a x b O _ _ _) as H.
  rewrite Nat.add_0_r in H.
  apply H.
Qed.

Fixpoint sideRL_rec(tm:TM)(l:list Sym)(r:side)(q:Q)(T:nat) :=
match T with
| O => None
| S T =>
  match r with
  | m>>r =>
    match tm (q,m) with
    | Some (m,L,q) =>
      match l with
      | m'::l => sideRL_rec tm l (m'>>m>>r) q T
      | [] => Some (q,m>>r)
      end
    | Some (m,R,q) => sideRL_rec tm (m::l) r q T
    | None => None
    end
  end
end.

Lemma sideRL_rec_spec tm l r q T q' r':
  sideRL_rec tm l r q T = Some (q',r') ->
  (forall l0, l0 <* l {{q}}> r -[tm]->+ l0 <{{q'}} r').
Proof.
  gen l r q q' r'.
  induction T; cbn[sideRL_rec]; intros.
  1: congruence.
  destruct r as [m r].
  destruct (tm (q,m)) as [[[m0 []] q0]|] eqn:E.
  - destruct l as [|m' l].
    + inverts H.
      do 2 econstructor; apply E.
    + eapply progress_step.
      1: econstructor; apply E.
      cbn.
      eapply IHT in H.
      apply H.
  - eapply progress_step.
    1: econstructor; apply E.
    cbn.
    eapply IHT in H.
    apply H.
  - congruence.
Qed.

Fixpoint Str_firstn{A}(n:nat)(r:Stream A) :=
match n with
| O => []
| S n => Streams.hd r :: Str_firstn n (Streams.tl r)
end.

Lemma Str_firstn_spec{A} n (r:Stream A):
  r = (Str_firstn n r) *> (Str_nth_tl n r).
Proof.
  gen r.
  induction n; intros; cbn.
  - trivial.
  - rewrite <-(IHn (Streams.tl r)).
    destruct r; trivial.
Qed.

Section eqb_sec.
Import Eqb.

Definition skip_prefix(r0:list Sym)(r:side) :=
let len := List.length r0 in
if Eqb.eqb r0 (Str_firstn len r) then Some (Str_nth_tl len r) else None.

Lemma skip_prefix_spec r0 r r':
  skip_prefix r0 r = Some r' ->
  r = r0 *> r'.
Proof.
  unfold skip_prefix.
  intros.
  destruct (eqb_spec r0 (Str_firstn (List.length r0) r)).
  2: congruence.
  inverts H.
  epose proof (Str_firstn_spec (List.length r0) r) as I1.
  rewrite <-e in I1.
  apply I1.
Qed.

Definition skip_prefix_list(r0 r:list Sym) :=
let len := List.length r0 in
if eqb r0 (firstn len r) then Some (skipn len r) else None.

Lemma skip_prefix_list_spec r0 r r':
  skip_prefix_list r0 r = Some r' ->
  r = r0 ++ r'.
Proof.
  unfold skip_prefix_list.
  intros.
  destruct (eqb_spec r0 (firstn (List.length r0) r)).
  2: congruence.
  inverts H.
  pose proof (firstn_skipn (length r0) r).
  congruence.
Qed.

Definition sideRL_c tm '(QR,qR) '(QL,qL) r T :=
sideRL_rec tm qR r QR T &&& (fun '(q',r') =>
if Eqb.eqb QL q' then
skip_prefix qL r'
else None
).

Lemma sideRL_c_spec tm hR hL r r' T:
  sideRL_c tm hR hL r T = Some r' ->
  sideRL tm hR hL r r'.
Proof.
  unfold sideRL_c,if_Some.
  intros.
  destruct hR as [QR qR].
  destruct hL as [QL qL].
  destruct (sideRL_rec tm qR r QR T) as [[q' r'0]|] eqn:E.
  2: congruence.
  destruct (eqb_spec QL q'); [subst|congruence].
  apply skip_prefix_spec in H.
  subst.
  intro l.
  unfold to_DH_config.
  eapply sideRL_rec_spec in E.
  apply E.
Qed.

Fixpoint sideRLs_c tm hs r T :=
match hs with
| [] => Some r
| (hR,hL)::hs => sideRL_c tm hR hL r T &&& (fun r => sideRLs_c tm hs r T)
end.

Lemma sideRLs_c_spec tm hs r r' r'0 T:
  sideRLs_c tm hs r T = Some r' ->
  r'=r'0 ->
  sideRLs tm hs r r'0.
Proof.
  gen r.
  induction hs; cbn[sideRLs_c]; intros.
  - inverts H.
    subst.
    constructor.
  - destruct a as [hR hL].
    subst.
    unfold if_Some in H.
    destruct (sideRL_c tm hR hL r T) eqn:E.
    2: inverts H.
    eapply sideRL_c_spec in E.
    apply IHhs in H; trivial.
    econstructor; eauto 1.
Qed.

End eqb_sec.

Module BoundedConfig.

Import Eqb.

Ltac destruct_spec_expr e f :=
match e with
| match ?a with _ => _ end => destruct_spec_expr a f
| if ?a then _ else _ => destruct_spec_expr a f
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 ?arg7 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6 arg7);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 =>
  pose proof (f arg1 arg2 arg3 arg4);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 =>
  pose proof (f arg1 arg2 arg3);
  destruct e
| ?a ?arg1 ?arg2 =>
  pose proof (f arg1 arg2);
  destruct e
| ?a ?arg1 =>
  pose proof (f arg1);
  destruct e
end.

Ltac destruct_spec f :=
match goal with
|- ?a => destruct_spec_expr a f
end.

Record T := {
  l: list Sym;
  r: list Sym;
  s: Q;
  sgn: dir;
}.

Definition to_config (x:T) (l0 r0:side) :=
let (l,r,s,sgn):=x in
match sgn with
| L => l0 <* r <{{s}} l *> r0
| R => l0 <* l {{s}}> r *> r0
end.

Section tm_ctx.
Hypothesis tm:TM.

Definition step(x:T):option T :=
let (l,r,s,sgn):=x in
match r with
| nil => None
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (Build_T (m'::l) r0 s' sgn')
    else
      Some (Build_T (m'::r0) l s' sgn')
  end
end.

Fixpoint steps(n:nat)(x:T) :=
match step x with
| None => Some x
| Some x =>
  match n with
  | O => None
  | S n => steps n x
  end
end.

Definition steps1 n x :=
match step x with
| None => Some (x,false)
| Some x =>
  steps n x &&& (fun x => Some (x,true))
end.

Definition step_r0inf(x:T):option T :=
let (l,r,s,sgn):=x in
match r with
| nil =>
  match sgn with
  | R =>
    match tm (s,s0) with
    | None => None
    | Some (m',sgn',s') =>
      if dir_eqb sgn sgn' then
        Some (Build_T (m'::l) nil s' sgn')
      else
        Some (Build_T (m'::nil) l s' sgn')
    end
  | _ => None
  end
| m::r0 =>
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    if dir_eqb sgn sgn' then
      Some (Build_T (m'::l) r0 s' sgn')
    else
      Some (Build_T (m'::r0) l s' sgn')
  end
end.

Fixpoint steps_r0inf(n:nat)(x:T) :=
match step_r0inf x with
| None => Some x
| Some x =>
  match n with
  | O => None
  | S n => steps_r0inf n x
  end
end.

Definition steps1_r0inf n x :=
match step_r0inf x with
| None => None
| Some x =>
  steps_r0inf n x
end.

Lemma step_spec x:
match step x with
| Some x' =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->
  to_config x' l0 r0
| None =>
  True
end.
Proof.
  destruct x as [l1 r1 s1 sgn1].
  unfold step.
  destruct r1 as [|m r1]; cbn; trivial.
  destruct (tm (s1,m)) as [[[m2 sgn2] s2]|] eqn:E; trivial.
    destruct sgn1,sgn2; cbn;
    econstructor; eauto.
Qed.

Lemma step_r0inf_spec x:
match step_r0inf x with
| Some x' =>
  forall l0,
  to_config x l0 (const s0) -[ tm ]->
  to_config x' l0 (const s0)
| None =>
  True
end.
Proof.
  destruct x as [l1 r1 s1 sgn1].
  unfold step_r0inf.
  destruct r1 as [|m r1]; cbn; trivial.
  - destruct sgn1; trivial.
    destruct (tm (s1,s0)) as [[[m2 sgn2] s2]|] eqn:E; trivial.
      destruct sgn2; cbn;
      econstructor; eauto.
  - destruct (tm (s1,m)) as [[[m2 sgn2] s2]|] eqn:E; trivial.
      destruct sgn1,sgn2; cbn;
      econstructor; eauto.
Qed.

Lemma steps_spec n x:
match steps n x with
| None => True
| Some (x') =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->*
  to_config x' l0 r0
end.
Proof.
  gen x.
  induction n; intros.
  - unfold steps.
    destruct_spec (step_spec); trivial.
  - cbn[steps].
    destruct_spec (step_spec); trivial.
    specialize (IHn t).
    destruct_spec steps; trivial.
    eauto.
Qed.

Lemma steps_r0inf_spec n x:
match steps_r0inf n x with
| None => True
| Some (x') =>
  forall l0,
  to_config x l0 (const s0) -[ tm ]->*
  to_config x' l0 (const s0)
end.
Proof.
  gen x.
  induction n; intros.
  - unfold steps_r0inf.
    destruct_spec (step_r0inf_spec); trivial.
  - cbn[steps_r0inf].
    destruct_spec (step_r0inf_spec); trivial.
    specialize (IHn t).
    destruct_spec steps_r0inf; trivial.
    eauto.
Qed.

Lemma steps1_spec n x:
match steps1 n x with
| None => True
| Some (x',false) =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->*
  to_config x' l0 r0
| Some (x',true) =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->+
  to_config x' l0 r0
end.
Proof.
  unfold steps1.
  destruct_spec (step_spec); trivial.
  unfold if_Some.
  destruct_spec (steps_spec); trivial.
  intros.
  eapply progress_intro; eauto 1.
Qed.

Lemma steps1_r0inf_spec n x:
  match steps1_r0inf n x with
  | Some x' =>
    forall l0,
    to_config x l0 (const s0) -[ tm ]->+
    to_config x' l0 (const s0)
  | None => True
  end.
Proof.
  unfold steps1_r0inf.
  destruct_spec (step_r0inf_spec); trivial.
  unfold if_Some.
  destruct_spec (steps_r0inf_spec); trivial.
  intros.
  eapply progress_intro; eauto 1.
Qed.

Fixpoint all0(a:list Sym):bool :=
match a with
| a0::a1 => eqb a0 s0 && all0 a1
| [] => true
end.

Lemma all0_spec a:
  all0 a = true -> a*>const s0 = const s0.
Proof.
  induction a; cbn[all0]; intros; trivial.
  destruct (eqb_spec a s0); [|inverts H].
  apply IHa in H.
  cbn.
  subst.
  rewrite H,<-const_unfold; trivial.
Qed.

Fixpoint eq_app_r0inf(a b:list Sym):bool :=
match a,b with
| a0::a1,b0::b1 => eqb a0 b0 && eq_app_r0inf a1 b1
| a0::a1,[] => all0 a
| [],_ => all0 b
end.

Lemma eq_app_r0inf_spec a b:
  eq_app_r0inf a b = true ->
  a*>const s0 = b*>const s0.
Proof.
  gen b.
  induction a; cbn[eq_app_r0inf]; intros.
  - apply all0_spec in H; cbn; congruence.
  - destruct b.
    + apply all0_spec in H.
      apply H.
    + destruct (eqb_spec a s2); [|inverts H].
      subst.
      apply IHa in H.
      cbn; congruence.
Qed.

Definition skip_prefix_list_r0inf(r0 r:list Sym) :=
let len := List.length r0 in
if eqb r0 (firstn len r) then Some (skipn len r) else
let len := List.length r in
if eqb r (firstn len r0) then
if all0 (skipn len r0) then Some [] else None
else None.

Lemma skip_prefix_list_r0inf_spec r0 r r':
  skip_prefix_list_r0inf r0 r = Some r' ->
  r*>const s0 = r0*>r'*>const s0.
Proof.
  unfold skip_prefix_list_r0inf.
  intros.
  destruct (eqb_spec r0 (firstn (length r0) r)); subst.
  - inverts H.
    pose proof (firstn_skipn (length r0) r).
    remember (length r0) as v1.
    clear Heqv1.
    subst.
    rewrite <-Str_app_assoc,H; trivial.
  - destruct (eqb_spec r (firstn (length r) r0)); subst.
    2: congruence.
    destruct (all0 (skipn (length r) r0)) eqn:E; [|inverts H].
    apply all0_spec in E.
    inverts H.
    pose proof (firstn_skipn (length r) r0).
    remember (length r) as v1.
    clear Heqv1.
    subst.
    remember (firstn v1 r0) as v2.
    remember (skipn v1 r0) as v3.
    clear Heqv2 Heqv3.
    subst.
    rewrite Str_app_assoc; cbn; congruence.
Qed.

Lemma steps1_spec' n x:
match steps1 n x with
| None => True
| Some (x',_) =>
  forall l0 r0,
  to_config x l0 r0 -[ tm ]->*
  to_config x' l0 r0
end.
Proof.
  destruct_spec (steps1_spec); trivial.
  destruct p,b; intros; auto 2 using progress_evstep.
Qed.

Fixpoint segRLs_c (ls1 ls2:list (DH0*DH0)) (w1 w2:list Sym) (T:nat) {struct T} :=
match T with
| O => false
| S T =>
match ls1 with
| ((QR,qR),(QL,qL))::ls1 =>
  match steps1 T (Build_T qR w1 QR R) with
  | Some (Build_T l r q R,flag) =>
    match ls2 with
    | ((QR',qR'),hL')::ls2 =>
      eqb r [] &&
      eqb q QR' &&
      match skip_prefix_list qR' l with
      | Some w1 => segLLs_c (QL,qL) ls1 hL' ls2 w1 w2 T
      | None => false
      end
    | [] => false
    end
  | Some (Build_T l r q L,true) =>
    eqb r [] &&
    eqb q QL &&
    match skip_prefix_list qL l with
    | Some w1 => segRLs_c ls1 ls2 w1 w2 T
    | None => false
    end
  | _ => false
  end
| [] =>
  eqb ls2 [] &&
  eqb w1 w2
end
end
with segLLs_c h1 ls1 h2 ls2 w1 w2 T {struct T} :=
match T with
| O => false
| S T =>
let '(QL,qL):=h2 in
match steps1 T (Build_T qL w1 QL L) with
| Some (Build_T l r q R,flag) =>
  match ls2 with
  | ((QR',qR'),hL')::ls2 =>
    eqb r [] &&
    eqb q QR' &&
    match skip_prefix_list qR' l with
    | Some w1 => segLLs_c h1 ls1 hL' ls2 w1 w2 T
    | None => false
    end
  | _ => false
  end
| Some (Build_T l r q L,flag) =>
  let '(QL0,qL0):=h1 in
  eqb r [] &&
  eqb q QL0 &&
  match skip_prefix_list qL0 l with
  | Some w1 => segRLs_c ls1 ls2 w1 w2 T
  | None => false
  end
| _ => false
end
end.

Lemma segRLs_LLs_c_spec T:
  (forall ls1 ls2 w1 w2, if segRLs_c ls1 ls2 w1 w2 T then segRLs tm ls1 ls2 w1 w2 else True) /\
  (forall h1 ls1 h2 ls2 w1 w2, if segLLs_c h1 ls1 h2 ls2 w1 w2 T then segLLs tm h1 ls1 h2 ls2 w1 w2 else True).
Proof with trivial.
  induction T; cbn[segRLs_c]; cbn[segLLs_c]; split; intros...
  - destruct IHT as [I1 I2].
    destruct ls1 as [|[[QR qR] [QL qL]] ls1].
    { destruct (eqb_spec ls2 [])...
      destruct (eqb_spec w1 w2)...
      subst.
      constructor. }
    pose proof (steps1_spec' T0 (Build_T qR w1 QR R)) as I3.
    destruct_spec steps1_spec...
    destruct p as [[] flag]...
    destruct sgn0.
    {
      destruct flag...
      destruct (eqb_spec r0 [])...
      destruct (eqb_spec s2 QL)...
      destruct_spec skip_prefix_list_spec...
      destruct (segRLs_c ls1 ls2 l1 w2 T0) eqn:E...
      epose proof (I1 _ _ _ _) as I1.
      rewrite E in I1.
      econstructor; eauto.
      unfold segRL; intros; cbn.
      specialize (H l2 r1).
      cbn in H.
      specialize (H0 _ eq_refl).
      subst.
      rewrite Str_app_assoc in H.
      apply H.
    }
    {
      clear H.
      rename I3 into H.
      destruct ls2 as [|[[QR' qR'] hL'] ls2]...
      destruct (eqb_spec r0 [])...
      destruct (eqb_spec s2 QR')...
      destruct_spec skip_prefix_list_spec...
      destruct (segLLs_c (QL,qL) ls1 hL' ls2 l1 w2 T0) eqn:E...
      epose proof (I2 _ _ _ _ _ _) as I2.
      rewrite E in I2.
      eapply segRLs_RR_LLs; eauto.
      unfold segRR; intros; cbn.
      specialize (H l2 r1).
      cbn in H.
      specialize (H0 _ eq_refl).
      subst.
      rewrite Str_app_assoc in H.
      apply H.
    }
  - destruct IHT as [I1 I2].
    destruct h2 as [QL qL].
    destruct_spec steps1_spec'...
    destruct p as [[] _].
    destruct sgn0.
    {
      destruct h1 as [QL0 qL0].
      destruct (eqb_spec r0 [])...
      destruct (eqb_spec s2 QL0)...
      destruct_spec skip_prefix_list_spec...
      destruct (segRLs_c ls1 ls2 l1 w2 T0) eqn:E...
      epose proof (I1 _ _ _ _) as I1.
      rewrite E in I1.
      eapply segLLs_LL_RLs; eauto.
      unfold segLL; intros; cbn.
      specialize (H l2 r1).
      cbn in H.
      specialize (H0 _ eq_refl).
      subst.
      rewrite Str_app_assoc in H.
      apply H.
    }
    {
      destruct ls2 as [|[[QR' qR'] hL'] ls2]...
      destruct (eqb_spec r0 [])...
      destruct (eqb_spec s2 QR')...
      destruct_spec skip_prefix_list_spec...
      destruct (segLLs_c h1 ls1 hL' ls2 l1 w2 T0) eqn:E...
      epose proof (I2 _ _ _ _ _ _) as I2.
      rewrite E in I2.
      eapply segLLs_LR_LLs; eauto.
      unfold segLR; intros; cbn.
      specialize (H l2 r1).
      cbn in H.
      specialize (H0 _ eq_refl).
      subst.
      rewrite Str_app_assoc in H.
      apply H.
    }
Qed.

Fixpoint sideRLs_c hs r r' T :=
match hs with
| [] => eq_app_r0inf r r'
| ((QR,qR),(QL,qL))::hs =>
  match steps1_r0inf T (Build_T qR r QR R) with
  | Some (Build_T l r QL' L) =>
    eqb r [] &&
    eqb QL QL' &&
    match skip_prefix_list_r0inf qL l with
    | Some r0 => sideRLs_c hs r0 r' T
    | None => false
    end
  | _ => false
  end
end.

Lemma sideRLs_c_spec hs r r' T:
  sideRLs_c hs r r' T = true ->
  sideRLs tm hs (r*>const s0) (r'*>const s0).
Proof.
  gen r.
  induction hs; cbn[sideRLs_c]; intros.
  - apply eq_app_r0inf_spec in H.
    rewrite H.
    constructor.
  - destruct a as [[QR qR] [QL qL]].
    epose proof (steps1_r0inf_spec T (Build_T qR r0 QR R)) as I1.
    destruct (steps1_r0inf T (Build_T qR r0 QR R)) as [[l r QL' []]|].
    2,3: congruence.
    destruct (eqb_spec r []); [subst|inverts H].
    destruct (eqb_spec QL QL'); [subst|inverts H].
    destruct (skip_prefix_list_r0inf qL l) as [r0'|] eqn:E; [|inverts H].
    apply skip_prefix_list_r0inf_spec in E.
    apply IHhs in H.
    econstructor; eauto.
    unfold sideRL.
    intro l0.
    specialize (I1 l0).
    cbn in I1; cbn.
    congruence.
Qed.

Lemma segRLs_c_spec ls1 ls2 w1 w2 T:
  segRLs_c ls1 ls2 w1 w2 T = true -> segRLs tm ls1 ls2 w1 w2.
Proof.
  epose proof (segRLs_LLs_c_spec T) as [I1 _].
  epose proof (I1 _ _ _ _) as I1.
  intros.
  rewrite H in I1.
  apply I1.
Qed.

End tm_ctx.

End BoundedConfig.

End Individual.


