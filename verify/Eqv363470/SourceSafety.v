From BusyCoq.Eqv363470 Require Import BB92 GuardCertificate.
From BusyCoq.Eqv363470 Require Import SourceCtx.
From BusyCoq.Eqv363470 Require Import GuardDirect.
From Coq Require Import Streams List.

From BusyCoq Require Import Individual62.
Module Source := Individual62.Enumerate.Permute.Flip.Compute.TM.
Module Monitor := Guard.DHTMFromTM.TM.

Definition source363 : Source.TM :=
  fun '(q,s) => match q,s with
  | A6,S092 => Some(S192,R,B6) | A6,S192 => Some(S192,L,C6)
  | B6,S092 => Some(S192,L,C6) | B6,S192 => Some(S092,R,D6)
  | C6,S092 => Some(S092,L,E6) | C6,S192 => Some(S192,L,A6)
  | D6,S092 => Some(S092,R,F6) | D6,S192 => Some(S192,R,A6)
  | E6,S092 => Some(S192,R,D6) | E6,S192 => Some(S092,L,A6)
  | F6,S092 => None | F6,S192 => Some(S092,R,B6)
  end.

Definition project_state (q:state92) : option state6 :=
  match q with
  | A92 => Some A6 | B92 => Some B6 | C92 => Some C6
  | D92 => Some D6 | E92 => Some E6 | F92 => Some F6
  | G92 => Some D6 | H92 => Some F6 | I92 => None
  end.

Definition related (c:state6 * Source.tape) (m:state92 * Monitor.tape) :=
  project_state (fst m) = Some(fst c) /\ snd c = snd m.

Lemma transition_simulation mq sq s w d sq' :
  project_state mq = Some sq ->
  source363 (sq,s) = Some(w,d,sq') ->
  monitor_guard_tm (mq,s) <> None ->
  exists mq', monitor_guard_tm (mq,s) = Some(w,d,mq') /\
              project_state mq' = Some sq'.
Proof.
  destruct mq,sq,s; cbn; intros Hq Hstep Hdefined;
    try discriminate; inversion Hstep; subst;
    try (exfalso; apply Hdefined; reflexivity);
    eexists; split; reflexivity.
Qed.

Lemma monitor_defined mq l s r :
  ~Monitor.halts monitor_guard_tm (mq,((l,s),r)) ->
  monitor_guard_tm (mq,s) <> None.
Proof.
  intros Hnonhalt Hundefined. apply Hnonhalt.
  exists O. exists (mq,((l,s),r)). split.
  - constructor.
  - exact Hundefined.
Qed.

Lemma source_step_simulates c c' m :
  related c m ->
  ~Monitor.halts monitor_guard_tm m ->
  Source.step source363 c c' ->
  exists m', Monitor.step monitor_guard_tm m m' /\ related c' m' /\
             ~Monitor.halts monitor_guard_tm m'.
Proof.
  intros Hrelated Hnonhalt Hstep.
  destruct Hstep as [q q' s s' l r Hraw | q q' s s' l r Hraw].
  - destruct m as [mq mt]. destruct Hrelated as [Hq Ht].
    cbn in Hq,Ht. subst mt.
    pose proof (monitor_defined mq l s r Hnonhalt) as Hdefined.
    destruct (transition_simulation mq q s s' L q' Hq Hraw Hdefined)
      as [mq' [Hmon Hproject]].
    exists (mq',Monitor.move_left ((l,s'),r)). split.
    + apply Monitor.step_left. exact Hmon.
    + split.
      * split; [exact Hproject|reflexivity].
      * intros Hhalts. apply Hnonhalt.
        eapply Monitor.halts_step; [exact Hhalts|].
        apply Monitor.step_left. exact Hmon.
  - destruct m as [mq mt]. destruct Hrelated as [Hq Ht].
    cbn in Hq,Ht. subst mt.
    pose proof (monitor_defined mq l s r Hnonhalt) as Hdefined.
    destruct (transition_simulation mq q s s' R q' Hq Hraw Hdefined)
      as [mq' [Hmon Hproject]].
    exists (mq',Monitor.move_right ((l,s'),r)). split.
    + apply Monitor.step_right. exact Hmon.
    + split.
      * split; [exact Hproject|reflexivity].
      * intros Hhalts. apply Hnonhalt.
        eapply Monitor.halts_step; [exact Hhalts|].
        apply Monitor.step_right. exact Hmon.
Qed.

Lemma source_prefix_simulates n c c' m :
  Source.multistep source363 n c c' ->
  related c m -> ~Monitor.halts monitor_guard_tm m ->
  exists m', Monitor.multistep monitor_guard_tm n m m' /\
             related c' m' /\ ~Monitor.halts monitor_guard_tm m'.
Proof.
  intros Hsteps. revert m.
  induction Hsteps as [c|n c c1 c2 Hstep Hsteps IH]; intros m Hrelated Hnonhalt.
  - exists m. split; [constructor|]. split; assumption.
  - destruct (source_step_simulates c c1 m Hrelated Hnonhalt Hstep)
      as [m1 [HMstep [HR1 HNH1]]].
    destruct (IH m1 HR1 HNH1) as [m2 [HMsteps [HR2 HNH2]]].
    exists m2. split.
    + eapply Monitor.multistep_S; eauto.
    + split; assumption.
Qed.

Theorem monitor_nonhalting_implies_source_guard
  (Hmonitor : ~Monitor.halts monitor_guard_tm Monitor.c0) :
  forall n l r,
  ~Source.multistep source363 n Source.c0
     (B6,((l,S192),Cons S092 (Cons S192 r))).
Proof.
  intros n l r Hsource.
  assert (Hinitial : related Source.c0 Monitor.c0) by (split; reflexivity).
  destruct (source_prefix_simulates n Source.c0
      (B6,((l,S192),Cons S092 (Cons S192 r))) Monitor.c0
      Hsource Hinitial Hmonitor) as [m [HM [HR HNH]]].
  destruct m as [mq mt]. destruct HR as [Hq Ht]. cbn in Hq,Ht. subst mt.
  destruct mq; cbn in Hq; try discriminate.
  apply HNH. exists (S(S O)).
  exists (H92,((Cons S092 (Cons S092 l),S192),r)). split.
  - eapply Monitor.multistep_S.
    + eapply Monitor.step_right. reflexivity.
    + eapply Monitor.multistep_S.
      * eapply Monitor.step_right. reflexivity.
      * constructor.
  - reflexivity.
Qed.

Corollary source363_B1_right01_unreachable : forall n l r,
  ~Source.multistep source363 n Source.c0
     (B6,((l,S192),Cons S092 (Cons S192 r))).
Proof.
  apply monitor_nonhalting_implies_source_guard.
  exact monitor_guard_does_not_halt_direct.
Qed.

Print Assumptions transition_simulation.
Print Assumptions source_prefix_simulates.
Print Assumptions monitor_nonhalting_implies_source_guard.
Print Assumptions source363_B1_right01_unreachable.
