(* Existing accepted pair439/600; all local paths retain arbitrary tape exteriors. *)
From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
From BusyCoq.EqvRegularPairs.Pair439 Require Import Frozen439 Projection.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.

Definition diamond_start (l r : Stream sym92) := (B6, (l, S092, Cons S092 r)).
Definition diamond_end (l r : Stream sym92) :=
  (E6, (Streams.tl l, Streams.hd l, Cons S192 (Cons S092 r))).

Theorem source_three_steps l r :
  RI.multistep frozen439 3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem mapped_target_one_step l r :
  RI.step mapped600 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem source_positive_diamond l r :
  RI.progress frozen439 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_progress with (n:=2). apply source_three_steps. Qed.
Theorem exact_positive_diamond l r :
  RI.progress frozen439 (diamond_start l r) (diamond_end l r) /\
  RI.progress mapped600 (diamond_start l r) (diamond_end l r).
Proof. split; [apply source_positive_diamond | apply RI.progress_base, mapped_target_one_step]. Qed.

Lemma common_cell q s : (q <> B6 \/ s <> S092) -> frozen439 (q,s) = mapped600 (q,s).
Proof. destruct q,s; cbn; intuition congruence. Qed.
Lemma common_step q l s r c' : (q <> B6 \/ s <> S092) ->
  RI.step mapped600 (q,(l,s,r)) c' -> RI.step frozen439 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.
Theorem same_undefined_cell q s :
  frozen439 (q,s) = None <-> mapped600 (q,s) = None.
Proof. destruct q,s; cbn; split; intros H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen439 RI.c0 c.
Definition next := RI.step_c mapped600.
Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen439 c c' /\ RI.progress mapped600 c c' /\ reachable c'.
Proof.
  intros HR Hnext. assert (HN : RI.step mapped600 c c').
  { apply RI.step_c_spec. exact Hnext. }
  assert (HM : RI.progress frozen439 c c').
  { destruct c as [q [[l s] r]].
    destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HN]).
    pose proof (frozen439_reachable_guard l r HR) as Hguard.
    destruct r as [b tail]. cbn in Hguard. subst b.
    cbn [next RI.step_c mapped600 RI.move_left] in Hnext. inversion Hnext; subst.
    exact (source_positive_diamond l tail). }
  split; [exact HM |]. split; [apply RI.progress_base; exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep. exact HM.
Qed.
Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen439 c /\ RI.halts mapped600 c.
Proof.
  intros _ Hnone. destruct c as [q [[l s] r]].
  destruct q,s; cbn [next RI.step_c mapped600] in Hnone; try discriminate.
  split; apply RI.halted_halts; reflexivity.
Qed.
Theorem mapped_halting_equivalence :
  RI.halts frozen439 RI.c0 <-> RI.halts mapped600 RI.c0.
Proof.
  pose proof (RI.halts_iff frozen439 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff mapped600 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen439 c c' /\ reachable c'
    | None => RI.halts frozen439 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress mapped600 c c' /\ reachable c'
    | None => RI.halts mapped600 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj2 (macro_none c HP Hnext)). }
  assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
  specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.

Definition rename600 q := match q with C6 => E6 | D6 => C6 | E6 => D6 | _ => q end.
Definition inverse600 q := match q with C6 => D6 | D6 => E6 | E6 => C6 | _ => q end.
Theorem rename600_left_inverse q : inverse600 (rename600 q) = q.
Proof. destruct q; reflexivity. Qed.
Theorem rename600_right_inverse q : rename600 (inverse600 q) = q.
Proof. destruct q; reflexivity. Qed.
Theorem rename600_initial : rename600 A6 = A6 /\ inverse600 A6 = A6.
Proof. split; reflexivity. Qed.
Theorem original_to_mapped : renames original600 mapped600 rename600.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q,s; cbn in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.
Theorem mapped_to_original : renames mapped600 original600 inverse600.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q,s; cbn in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.
Theorem original_target_transport :
  RI.halts original600 RI.c0 <-> RI.halts mapped600 RI.c0.
Proof.
  split.
  - intro H. exact (transport_halts original600 mapped600 rename600 RI.c0 original_to_mapped H).
  - intro H. exact (transport_halts mapped600 original600 inverse600 RI.c0 mapped_to_original H).
Qed.
Theorem original439_600_halting_equivalence :
  RI.halts frozen439 RI.c0 <-> RI.halts original600 RI.c0.
Proof. pose proof mapped_halting_equivalence. pose proof original_target_transport. tauto. Qed.

Print Assumptions source_three_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions mapped_halting_equivalence.
Print Assumptions rename600_left_inverse.
Print Assumptions rename600_right_inverse.
Print Assumptions rename600_initial.
Print Assumptions original_to_mapped.
Print Assumptions mapped_to_original.
Print Assumptions original_target_transport.
Print Assumptions original439_600_halting_equivalence.
