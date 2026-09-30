(* Existing accepted pair3/751; all local paths retain arbitrary tape exteriors. *)
From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import EndpointEncoding.
From BusyCoq.EqvRegularPairs.Pair3 Require Import Frozen3 Projection.
From BusyCoq.EqvRegularPairs Require Import StateTransport.
Close Scope sym_scope.
Open Scope nat_scope.

Definition diamond_start (l r : Stream sym92) := (D6, (Cons S092 l, S092, r)).
Definition diamond_end (l r : Stream sym92) :=
  (F6, (Cons S192 (Cons S092 l), Streams.hd r, Streams.tl r)).

Theorem source_three_steps l r :
  RI.multistep frozen3 3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem mapped_target_one_step l r :
  RI.step mapped751 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem source_positive_diamond l r :
  RI.progress frozen3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_progress with (n:=2). apply source_three_steps. Qed.
Theorem exact_positive_diamond l r :
  RI.progress frozen3 (diamond_start l r) (diamond_end l r) /\
  RI.progress mapped751 (diamond_start l r) (diamond_end l r).
Proof. split; [apply source_positive_diamond | apply RI.progress_base, mapped_target_one_step]. Qed.

Lemma common_cell q s : (q <> D6 \/ s <> S092) -> frozen3 (q,s) = mapped751 (q,s).
Proof. destruct q,s; cbn; intuition congruence. Qed.
Lemma common_step q l s r c' : (q <> D6 \/ s <> S092) ->
  RI.step mapped751 (q,(l,s,r)) c' -> RI.step frozen3 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.
Theorem same_undefined_cell q s :
  frozen3 (q,s) = None <-> mapped751 (q,s) = None.
Proof. destruct q,s; cbn; split; intros H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen3 RI.c0 c.
Definition next := RI.step_c mapped751.
Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen3 c c' /\ RI.progress mapped751 c c' /\ reachable c'.
Proof.
  intros HR Hnext. assert (HN : RI.step mapped751 c c').
  { apply RI.step_c_spec. exact Hnext. }
  assert (HM : RI.progress frozen3 c c').
  { destruct c as [q [[l s] r]].
    destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HN]).
    pose proof (frozen3_reachable_guard l r HR) as Hguard.
    destruct l as [b tail]. cbn in Hguard. subst b.
    cbn [next RI.step_c mapped751 RI.move_right] in Hnext. inversion Hnext; subst.
    exact (source_positive_diamond tail r). }
  split; [exact HM |]. split; [apply RI.progress_base; exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep. exact HM.
Qed.
Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen3 c /\ RI.halts mapped751 c.
Proof.
  intros _ Hnone. destruct c as [q [[l s] r]].
  destruct q,s; cbn [next RI.step_c mapped751] in Hnone; try discriminate.
  split; apply RI.halted_halts; reflexivity.
Qed.
Theorem mapped_halting_equivalence :
  RI.halts frozen3 RI.c0 <-> RI.halts mapped751 RI.c0.
Proof.
  pose proof (RI.halts_iff frozen3 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff mapped751 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen3 c c' /\ reachable c'
    | None => RI.halts frozen3 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress mapped751 c c' /\ reachable c'
    | None => RI.halts mapped751 c end).
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
Theorem original_to_mapped : renames original751 mapped751 swapEF.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q,s; cbn in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.
Theorem mapped_to_original : renames mapped751 original751 swapEF.
Proof.
  split.
  - intros q s H. destruct q,s; cbn in *; try discriminate; reflexivity.
  - intros q s s' d q' H. destruct q,s; cbn in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.
Theorem original_target_transport :
  RI.halts original751 RI.c0 <-> RI.halts mapped751 RI.c0.
Proof.
  split.
  - intro H. exact (transport_halts original751 mapped751 swapEF RI.c0 original_to_mapped H).
  - intro H. exact (transport_halts mapped751 original751 swapEF RI.c0 mapped_to_original H).
Qed.
Theorem original3_751_halting_equivalence :
  RI.halts frozen3 RI.c0 <-> RI.halts original751 RI.c0.
Proof. pose proof mapped_halting_equivalence. pose proof original_target_transport. tauto. Qed.

Print Assumptions source_three_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions mapped_halting_equivalence.
Print Assumptions swapEF_involutive.
Print Assumptions original_to_mapped.
Print Assumptions mapped_to_original.
Print Assumptions original_target_transport.
Print Assumptions original3_751_halting_equivalence.
