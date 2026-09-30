From BusyCoq.Eqv363470 Require Import BB92 GuardCertificate.
From BusyCoq.Eqv363470 Require Import SourceCtx SourceSafety.
From Coq Require Import Streams List.

Definition target470 : Source.TM :=
  fun '(q,s) => match q,s with
  | A6,S092 => Some(S192,R,B6) | A6,S192 => Some(S192,L,C6)
  | B6,S092 => Some(S192,L,C6) | B6,S192 => Some(S092,R,D6)
  | C6,S092 => Some(S092,L,E6) | C6,S192 => Some(S192,L,A6)
  | D6,S092 => None | D6,S192 => Some(S192,R,A6)
  | E6,S092 => Some(S192,R,F6) | E6,S192 => Some(S092,L,A6)
  | F6,S092 => Some(S092,R,F6) | F6,S192 => Some(S092,R,B6)
  end.

Definition predecessor_context (c:state6 * Source.tape) :=
  let '(q,((l,s),r)) := c in
  match q with
  | C6 => Streams.hd r = S192
  | E6 => Streams.hd r = S092 /\ Streams.hd(Streams.tl r) = S192
  | _ => True
  end.

Lemma predecessor_context_step c c' :
  predecessor_context c -> Source.step source363 c c' ->
  predecessor_context c'.
Proof.
  intros HP HS.
  destruct HS as [q q' s s' l r HT |q q' s s' l r HT];
    destruct q,s; cbn [source363] in HT; try discriminate;
    inversion HT; subst; cbn [predecessor_context Source.move_left Source.move_right] in *;
    repeat split; auto.
Qed.

Lemma predecessor_context_evstep c c' :
  Source.evstep source363 c c' -> predecessor_context c -> predecessor_context c'.
Proof.
  intros H. induction H; intros HP.
  - exact HP.
  - apply IHevstep. eapply predecessor_context_step; eauto.
Qed.

Lemma reachable_predecessor_context c :
  Source.evstep source363 Source.c0 c -> predecessor_context c.
Proof.
  intros H. eapply predecessor_context_evstep; [exact H|]. exact I.
Qed.

Definition boundary (c:state6 * Source.tape) :=
  let '(q,((l,s),r)) := c in
  match q,s with D6,S092 | F6,S092 => False | _,_ => True end.
Definition boundary_reachable c := Source.evstep source363 Source.c0 c /\ boundary c.
Definition source_guard := forall n l r,
  ~Source.multistep source363 n Source.c0
    (B6,((l,S192),Cons S092 (Cons S192 r))).

Definition macro_next (c:state6 * Source.tape) : option(state6 * Source.tape) :=
  let '(q,((l,s),r)) := c in
  match q,s with
  | E6,S092 => Some(F6,((Cons S092 (Cons S192 l),Streams.hd(Streams.tl r)),Streams.tl(Streams.tl r)))
  | B6,S192 => match Streams.hd r with S092 => None | S192 => Source.step_c source363 c end
  | D6,S092 | F6,S092 => None
  | _,_ => Source.step_c source363 c
  end.

Lemma continuing_macro c c' :
  Source.evstep source363 Source.c0 c ->
  Source.progress source363 c c' -> Source.progress target470 c c' -> boundary c' ->
  Source.progress source363 c c' /\ Source.progress target470 c c' /\ boundary_reachable c'.
Proof.
  intros HR HM HN HB. split; [exact HM|]. split; [exact HN|].
  split; [|exact HB]. eapply Source.evstep_trans; [exact HR|].
  apply Source.progress_evstep. exact HM.
Qed.

Lemma common_one_step c c' :
  Source.evstep source363 Source.c0 c ->
  Source.step source363 c c' -> Source.step target470 c c' -> boundary c' ->
  Source.progress source363 c c' /\ Source.progress target470 c c' /\ boundary_reachable c'.
Proof.
  intros HR HM HN HB. apply continuing_macro; try assumption;
    apply Source.progress_base; assumption.
Qed.

Ltac ordinary_common_case HR :=
  eapply common_one_step;
  [exact HR
  |first [eapply Source.step_left; reflexivity|eapply Source.step_right; reflexivity]
  |first [eapply Source.step_left; reflexivity|eapply Source.step_right; reflexivity]
  |exact I].

Section Coupling.
Hypothesis Hguard : source_guard.

Lemma reachable_B101_excluded l r :
  ~Source.evstep source363 Source.c0
    (B6,((l,S192),Cons S092 (Cons S192 r))).
Proof.
  intros H. apply Source.evstep_multistep in H. destruct H as [n H].
  eapply Hguard. exact H.
Qed.

Lemma macro_correct c : boundary_reachable c ->
  match macro_next c with
  | Some c' => Source.progress source363 c c' /\
               Source.progress target470 c c' /\ boundary_reachable c'
  | None => Source.halts source363 c /\ Source.halts target470 c
  end.
Proof.
  destruct c as [q [[l s] r]]. intros [HR HB].
  destruct q,s; cbn [macro_next Source.step_c source363] in *.
  - ordinary_common_case HR.
  - ordinary_common_case HR.
  - ordinary_common_case HR.
  - destruct r as [x rt]. destruct x.
    + destruct rt as [y rr]. destruct y.
      * split.
        -- exists (S(S O)). exists(F6,((Cons S092 (Cons S092 l),S092),rr)). split.
           ++ eapply Source.multistep_S.
              ** eapply Source.step_right. reflexivity.
              ** eapply Source.multistep_S.
                 --- eapply Source.step_right. reflexivity.
                 --- constructor.
           ++ reflexivity.
        -- exists (S O). exists(D6,((Cons S092 l,S092),Cons S092 rr)). split.
           ++ eapply Source.multistep_S.
              ** eapply Source.step_right. reflexivity.
              ** constructor.
           ++ reflexivity.
      * exfalso. eapply reachable_B101_excluded. exact HR.
    + cbn [Streams.hd]. ordinary_common_case HR.
  - ordinary_common_case HR.
  - ordinary_common_case HR.
  - contradiction.
  - ordinary_common_case HR.
  - pose proof (reachable_predecessor_context _ HR) as HP.
    destruct r as [x rt]. destruct rt as [y rr].
    cbn [predecessor_context Streams.hd Streams.tl] in HP. destruct HP as [Hx Hy]. subst x y.
    cbn [Streams.hd Streams.tl]. eapply continuing_macro; [exact HR| | |exact I].
    + eapply Source.progress_step.
      * eapply Source.step_right. reflexivity.
      * cbn [Source.move_right Streams.hd Streams.tl].
        apply Source.progress_base.
        apply (@Source.step_right source363 D6 F6 S092 S092 (Cons S192 l) (Cons S192 rr)). reflexivity.
    + eapply Source.progress_step.
      * eapply Source.step_right. reflexivity.
      * cbn [Source.move_right Streams.hd Streams.tl].
        apply Source.progress_base.
        apply (@Source.step_right target470 F6 F6 S092 S092 (Cons S192 l) (Cons S192 rr)). reflexivity.
  - ordinary_common_case HR.
  - contradiction.
  - ordinary_common_case HR.
Qed.

Theorem halting_equivalence_if_guard :
  Source.halts source363 Source.c0 <-> Source.halts target470 Source.c0.
Proof.
  assert (HP0 : boundary_reachable Source.c0) by (split; [constructor|exact I]).
  pose proof (Source.halts_iff source363 _ Source.c0 macro_next (fun c=>c)
    boundary_reachable) as HM.
  pose proof (Source.halts_iff target470 _ Source.c0 macro_next (fun c=>c)
    boundary_reachable) as HN.
  assert (HMs : forall i, boundary_reachable i ->
    match macro_next i with
    | Some j => Source.progress source363 i j /\ boundary_reachable j
    | None => Source.halts source363 i end).
  { intros i HP. pose proof (macro_correct i HP) as H.
    destruct (macro_next i); tauto. }
  assert (HNs : forall i, boundary_reachable i ->
    match macro_next i with
    | Some j => Source.progress target470 i j /\ boundary_reachable j
    | None => Source.halts target470 i end).
  { intros i HP. pose proof (macro_correct i HP) as H.
    destruct (macro_next i); tauto. }
  specialize (HM HMs HP0). specialize (HN HNs HP0). tauto.
Qed.
End Coupling.

Theorem original363_470_halting_equivalence :
  Source.halts source363 Source.c0 <-> Source.halts target470 Source.c0.
Proof.
  apply halting_equivalence_if_guard.
  exact source363_B1_right01_unreachable.
Qed.

Print Assumptions predecessor_context_step.
Print Assumptions halting_equivalence_if_guard.
Print Assumptions original363_470_halting_equivalence.
