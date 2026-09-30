(* Existing accepted pair70/223. The exceptional macro branch proves paired
   finite halting; it deliberately does not assert equal final tapes. *)
From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
From BusyCoq.EqvRegularPairs.Pair70 Require Import Frozen70 Projection.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.

Definition diamond_start (l r : Stream sym92) := (B6,(Cons S192 l,S092,r)).
Definition diamond_end (l r : Stream sym92) :=
  (C6,(Cons S092 (Cons S192 l),Streams.hd r,Streams.tl r)).
Theorem source_five_steps l r :
  RI.multistep frozen70 5 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem target_one_step l r :
  RI.step mapped223 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem source_positive_diamond l r :
  RI.progress frozen70 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_progress with (n:=4). apply source_five_steps. Qed.
Theorem exact_positive_diamond l r :
  RI.progress frozen70 (diamond_start l r) (diamond_end l r) /\
  RI.progress mapped223 (diamond_start l r) (diamond_end l r).
Proof. split; [apply source_positive_diamond | apply RI.progress_base,target_one_step]. Qed.

Definition terminal_start (r : Stream sym92) := (B6,(const S092,S092,Cons S092 r)).
Definition source_terminal_end (r : Stream sym92) :=
  (E6,(Cons S192 (Cons S192 (const S092)),S192,Cons S192 (Cons S092 r))).
Definition target_terminal_end (r : Stream sym92) :=
  (E6,(Cons S192 (Cons S192 (const S092)),S192,r)).
Theorem source_five_terminal_steps r :
  RI.multistep frozen70 5 (terminal_start r) (source_terminal_end r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem target_five_terminal_steps r :
  RI.multistep mapped223 5 (terminal_start r) (target_terminal_end r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem paired_terminal_halts r :
  RI.halts frozen70 (terminal_start r) /\ RI.halts mapped223 (terminal_start r).
Proof.
  split.
  - eapply RI.halts_multistep with (c':=source_terminal_end r) (n:=5); [apply RI.halted_halts; reflexivity | apply source_five_terminal_steps].
  - eapply RI.halts_multistep with (c':=target_terminal_end r) (n:=5); [apply RI.halted_halts; reflexivity | apply target_five_terminal_steps].
Qed.

Lemma common_cell q s : (q <> B6 \/ s <> S092) -> frozen70 (q,s) = mapped223 (q,s).
Proof. destruct q,s; cbn; intuition congruence. Qed.
Lemma common_step q l s r c' : (q <> B6 \/ s <> S092) ->
  RI.step mapped223 (q,(l,s,r)) c' -> RI.step frozen70 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.
Theorem same_undefined_cell q s :
  frozen70 (q,s) = None <-> mapped223 (q,s) = None.
Proof. destruct q,s; cbn; split; intro H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen70 RI.c0 c.
Definition next (c : state6 * RI.tape) :=
  match c with
  | (B6,(l,S092,r)) => match Streams.hd l with
      | S092 => None | S192 => RI.step_c mapped223 c end
  | _ => RI.step_c mapped223 c
  end.
Lemma next_some_step c c' : next c = Some c' -> RI.step mapped223 c c'.
Proof.
  destruct c as [q [[l s] r]]. destruct q,s; cbn [next]; intro H;
    try (apply RI.step_c_spec; exact H).
  destruct l as [b tail]. destruct b; cbn in H; try discriminate.
  apply RI.step_c_spec. exact H.
Qed.
Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen70 c c' /\ RI.progress mapped223 c c' /\ reachable c'.
Proof.
  intros HR Hnext. pose proof (next_some_step c c' Hnext) as HN.
  assert (HM : RI.progress frozen70 c c').
  { destruct c as [q [[l s] r]].
    destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HN]).
    destruct l as [b tail]. destruct b; cbn [next] in Hnext; try discriminate.
    cbn [RI.step_c mapped223 RI.move_right] in Hnext. inversion Hnext; subst.
    exact (source_positive_diamond tail r). }
  split; [exact HM |]. split; [apply RI.progress_base; exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep. exact HM.
Qed.
Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen70 c /\ RI.halts mapped223 c.
Proof.
  intros HR Hnone. destruct c as [q [[l s] r]].
  destruct q,s; cbn [next RI.step_c mapped223] in Hnone; try discriminate.
  - pose proof (frozen70_reachable_guard l r HR) as HG.
    destruct l as [b tail]. destruct b; cbn in Hnone; try discriminate.
    destruct HG as [Hone|[Hblank Hr]].
    + discriminate Hone.
    + rewrite Hblank. destruct r as [rb rt]. cbn in Hr. subst rb.
      exact (paired_terminal_halts rt).
  - split; apply RI.halted_halts; reflexivity.
Qed.
Theorem mapped_halting_equivalence :
  RI.halts frozen70 RI.c0 <-> RI.halts mapped223 RI.c0.
Proof.
  pose proof (RI.halts_iff frozen70 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff mapped223 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen70 c c' /\ reachable c'
    | None => RI.halts frozen70 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress mapped223 c c' /\ reachable c'
    | None => RI.halts mapped223 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj2 (macro_none c HP Hnext)). }
  assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
  specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.
Definition swapEF q := match q with E6 => F6 | F6 => E6 | _ => q end.
Theorem swapEF_involutive q : swapEF (swapEF q) = q.
Proof. destruct q; reflexivity. Qed.
Theorem swapEF_initial : swapEF A6 = A6.
Proof. reflexivity. Qed.
Theorem original_to_mapped : renames original223 mapped223 swapEF.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s w d q' H. destruct q,s; cbn in H; try discriminate; inversion H; subst; reflexivity.
Qed.
Theorem mapped_to_original : renames mapped223 original223 swapEF.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s w d q' H. destruct q,s; cbn in H; try discriminate; inversion H; subst; reflexivity.
Qed.
Theorem original_target_transport :
  RI.halts original223 RI.c0 <-> RI.halts mapped223 RI.c0.
Proof.
  split; intro H.
  - exact (transport_halts original223 mapped223 swapEF RI.c0 original_to_mapped H).
  - exact (transport_halts mapped223 original223 swapEF RI.c0 mapped_to_original H).
Qed.
Theorem original70_223_halting_equivalence :
  RI.halts frozen70 RI.c0 <-> RI.halts original223 RI.c0.
Proof. pose proof mapped_halting_equivalence. pose proof original_target_transport. tauto. Qed.

Print Assumptions source_five_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions source_five_terminal_steps.
Print Assumptions target_five_terminal_steps.
Print Assumptions paired_terminal_halts.
Print Assumptions next_some_step.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions mapped_halting_equivalence.
Print Assumptions swapEF_involutive.
Print Assumptions original_to_mapped.
Print Assumptions mapped_to_original.
Print Assumptions original_target_transport.
Print Assumptions original70_223_halting_equivalence.

(* Complete assumption inventory for this unit. *)
Print Assumptions target_one_step.
Print Assumptions source_positive_diamond.
Print Assumptions common_cell.
Print Assumptions common_step.
Print Assumptions same_undefined_cell.
Print Assumptions swapEF_initial.
