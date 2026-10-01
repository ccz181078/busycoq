(* Original408 versus the exactly aligned published intermediate Q. *)
From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv326408 Require Import Frozen408.
From BusyCoq.Eqv326408 Require Import Projection.
Close Scope sym_scope.
Open Scope nat_scope.

Definition diamond_start (l : Stream sym92) (b : sym92) (r : Stream sym92) :=
 (A6,(Cons b l,S092,Cons S092 r)).
Definition diamond_end (l : Stream sym92) (b : sym92) (r : Stream sym92) :=
 (D6,(l,b,Cons S192 (Cons S092 r))).
Theorem source_three_steps l b r : RI.multistep frozen408 3 (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem target_one_step l b r : RI.step alignedQ (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem source_positive_diamond l b r : RI.progress frozen408 (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.multistep_progress with (n:=2). apply source_three_steps. Qed.
Theorem exact_positive_diamond l b r : RI.progress frozen408 (diamond_start l b r) (diamond_end l b r) /\ RI.progress alignedQ (diamond_start l b r) (diamond_end l b r).
Proof. split; [apply source_positive_diamond|apply RI.progress_base,target_one_step]. Qed.

Lemma common_cell q s : (q <> A6 \/ s <> S092) -> frozen408 (q,s) = alignedQ (q,s).
Proof. destruct q, s; cbn; intuition congruence. Qed.

Lemma common_step q l s r c' : (q <> A6 \/ s <> S092) ->
  RI.step alignedQ (q,(l,s,r)) c' -> RI.step frozen408 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q, s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.

Theorem same_undefined_cell q s :
  frozen408 (q,s) = None <-> alignedQ (q,s) = None.
Proof. destruct q, s; cbn; split; intros H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen408 RI.c0 c.
Definition next := RI.step_c alignedQ.

Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen408 c c' /\ RI.progress alignedQ c c' /\ reachable c'.
Proof.
  intros HR Hnext. assert (HN : RI.step alignedQ c c').
  { apply RI.step_c_spec. exact Hnext. }
  assert (HM : RI.progress frozen408 c c').
  { destruct c as [q [[l s] r]].
    destruct q, s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HN]).
    pose proof (frozen408_reachable_guard l r HR) as Hguard.
    destruct r as [b tail]. cbn in Hguard. subst b. destruct l as [leftbit lefttail].
    cbn [next RI.step_c alignedQ RI.move_left] in Hnext. inversion Hnext; subst.
    exact (source_positive_diamond lefttail leftbit tail). }
  split; [exact HM |]. split; [apply RI.progress_base; exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep. exact HM.
Qed.

Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen408 c /\ RI.halts alignedQ c.
Proof.
  intros _ Hnone. destruct c as [q [[l s] r]].
  destruct q, s; cbn [next RI.step_c alignedQ] in Hnone; try discriminate.
  split; apply RI.halted_halts; reflexivity.
Qed.

Theorem internal408_aligned_halting_equivalence :
  RI.halts frozen408 RI.c0 <-> RI.halts alignedQ RI.c0.
Proof.
  pose proof (RI.halts_iff frozen408 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff alignedQ (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen408 c c' /\ reachable c'
    | None => RI.halts frozen408 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress alignedQ c c' /\ reachable c'
    | None => RI.halts alignedQ c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj2 (macro_none c HP Hnext)). }
  assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
  specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.

Print Assumptions source_three_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions internal408_aligned_halting_equivalence.
