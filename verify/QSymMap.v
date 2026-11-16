From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From BusyCoq Require Import TM.
Set Default Goal Selector "!".

Module QSymMap(Ctx0 Ctx1:Ctx).
Module TM0 := TM Ctx0.
Module TM1 := TM Ctx1.

Section from_ctx.
Hypothesis from:
  (Ctx0.Q*Ctx0.Sym->option (Ctx0.Sym*dir*Ctx0.Q)) ->
  (Ctx1.Q*Ctx1.Sym->option (Ctx1.Sym*dir*Ctx1.Q)).
Hypothesis Fq:Ctx1.Q->Ctx0.Q.
Hypothesis Fsym:Ctx1.Sym->Ctx0.Sym.

Hypothesis HFq0:
  Fq Ctx1.q0 = Ctx0.q0.
Hypothesis HFs0:
  Fsym Ctx1.s0 = Ctx0.s0.
Hypothesis Hfrom:
  forall tm0 q s,
  tm0 (Fq q,Fsym s) =
  match from tm0 (q,s) with
  | Some (s',d,q') => Some (Fsym s',d,Fq q')
  | None => None
  end.

Inductive Fside:TM1.side->TM0.side->Prop :=
| Fside_O:
  Fside (const Ctx1.s0) (const Ctx0.s0)
| Fside_S a0 a1 b1:
  Fside a1 b1 ->
  Fside (a0>>a1) ((Fsym a0)>>b1).

Inductive Fconfig:Ctx1.Q*TM1.tape -> Ctx0.Q*TM0.tape -> Prop :=
| Fconfig_intro q1 l1 m1 r1 l2 r2:
  Fside l1 l2 ->
  Fside r1 r2 ->
  Fconfig (q1,(l1,m1,r1)) (Fq q1,(l2,Fsym m1,r2)).

Lemma from_step {tm c1 c2 c1'}:
  Fconfig c1' c1 ->
  TM0.step tm c1 c2 ->
  exists c2',
  Fconfig c2' c2 /\
  TM1.step (from tm) c1' c2'.
Proof.
  intros Hc Hs.
  inverts Hc.
  specialize (Hfrom tm q1 m1).
  inverts Hs.
  - destruct (from tm (q1,m1)) as [[[s'' d] q'']|] eqn:E.
    2: congruence.
    inverts H.
    + eexists.
      split.
      2:{
        eapply TM1.step_left.
        cbn.
        rewrite H6 in Hfrom.
        rewrite E.
        repeat f_equal.
        congruence.
      }
      applys_eq Fconfig_intro; cbn.
      2,3: econstructor; eauto.
      congruence.
    + eexists.
      split.
      2:{
        eapply TM1.step_left.
        cbn.
        rewrite H6 in Hfrom.
        rewrite E.
        repeat f_equal.
        congruence.
      }
      applys_eq Fconfig_intro; cbn.
      2: eauto.
      2: econstructor; eauto.
      congruence.
  - destruct (from tm (q1,m1)) as [[[s'' d] q'']|] eqn:E.
    2: congruence.
    inverts H0.
    + eexists.
      split.
      2:{
        eapply TM1.step_right.
        cbn.
        rewrite H6 in Hfrom.
        rewrite E.
        repeat f_equal.
        congruence.
      }
      applys_eq Fconfig_intro; cbn.
      2,3: econstructor; eauto.
      congruence.
    + eexists.
      split.
      2:{
        eapply TM1.step_right.
        cbn.
        rewrite H6 in Hfrom.
        rewrite E.
        repeat f_equal.
        congruence.
      }
      applys_eq Fconfig_intro; cbn.
      3: eauto.
      2: econstructor; eauto.
      congruence.
Qed.

Lemma from_multistep {tm n c1 c2 c1'}:
  Fconfig c1' c1 ->
  TM0.multistep tm n c1 c2 ->
  exists c2',
  Fconfig c2' c2 /\
  TM1.multistep (from tm) n c1' c2'.
Proof.
  gen c1 c2 c1'.
  induction n; intros.
  - inverts H0.
    exists c1'.
    split.
    1: tauto.
    constructor.
  - inverts H0.
    pose proof (from_step H H2) as [c2' [Hc Hs]].
    specialize (IHn _ _ _ Hc H3).
    destruct IHn as [c3' [Hc' Hs']].
    exists c3'.
    split; eauto.
    econstructor; eauto.
Qed.

Lemma from_c0:
  Fconfig TM1.c0 TM0.c0.
Proof.
  unfold TM0.c0,TM0.tape0.
  applys_eq Fconfig_intro.
  1: repeat f_equal; try congruence.
  1,2: constructor.
Qed.

Lemma from_spec(tm:TM0.TM):
  TM0.halts tm TM0.c0 ->
  TM1.halts (from tm) TM1.c0.
Proof.
  unfold TM0.halts,TM0.halts_in.
  unfold TM1.halts,TM1.halts_in.
  intros [n [ch [H H0]]].
  pose proof (from_multistep from_c0 H) as [c2' [Hc Hs]].
  exists n c2'.
  split; auto.
  inverts Hc.
  cbn in *.
  specialize (Hfrom tm q1 m1).
  rewrite H0 in Hfrom.
  destruct (from tm (q1,m1)) as [[[s'' d] q'']|]; try congruence.
Qed.

Lemma from_nonhalt tm:
  ~TM1.halts' (from tm) TM1.c0 ->
  ~TM0.halts' tm TM0.c0.
Proof.
  rewrite <-TM0.halts_halts'.
  rewrite <-TM1.halts_halts'.
  pose proof (from_spec tm).
  tauto.
Qed.

End from_ctx.

End QSymMap.
