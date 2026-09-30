From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv464572 Require Import Frozen464Indexed Projection.
Close Scope sym_scope.
Open Scope nat_scope.

Definition diamond_start (l : Stream sym92) (b : sym92) (r : Stream sym92) :=
  (F6,(Cons S092 (Cons S192 l),S192,Cons b r)).
Definition diamond_end (l : Stream sym92) (b : sym92) (r : Stream sym92) :=
  (C6,(Cons S092 (Cons S092 (Cons S192 l)),b,r)).

Theorem source_one_step l b r :
  RI.step frozen464 (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.step_c_spec. reflexivity. Qed.

Theorem target_seven_steps l b r :
  RI.multistep frozen572 7 (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.

Theorem target_positive_diamond l b r :
  RI.progress frozen572 (diamond_start l b r) (diamond_end l b r).
Proof. apply RI.multistep_progress with (n:=6). apply target_seven_steps. Qed.

Theorem exact_positive_diamond l b r :
  RI.progress frozen464 (diamond_start l b r) (diamond_end l b r) /\
  RI.progress frozen572 (diamond_start l b r) (diamond_end l b r).
Proof. split; [apply RI.progress_base, source_one_step | apply target_positive_diamond]. Qed.

Lemma common_step q l s r c' : (q <> F6 \/ s <> S192) ->
  RI.step frozen464 (q,(l,s,r)) c' -> RI.step frozen572 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.

Theorem same_undefined_cell q s :
  frozen464 (q,s) = None <-> frozen572 (q,s) = None.
Proof. destruct q,s; cbn; split; intros H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen464 RI.c0 c.
Definition next := RI.step_c frozen464.

Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen464 c c' /\ RI.progress frozen572 c c' /\ reachable c'.
Proof.
  intros HR Hnext. assert (HM : RI.step frozen464 c c').
  { apply RI.step_c_spec. exact Hnext. }
  assert (HN : RI.progress frozen572 c c').
  { destruct c as [q [[l s] r]].
    destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HM]).
    pose proof (frozen464_reachable_guard l r HR) as [Hfirst Hsecond].
    destruct l as [x tail]. destruct tail as [y rest].
    cbn in Hfirst,Hsecond. subst x y. destruct r as [b rt].
    cbn [next RI.step_c frozen464 RI.move_right] in Hnext. inversion Hnext; subst.
    exact (target_positive_diamond rest b rt). }
  split; [apply RI.progress_base; exact HM |]. split; [exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep, RI.progress_base. exact HM.
Qed.

Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen464 c /\ RI.halts frozen572 c.
Proof.
  intros _ Hnone. destruct c as [q [[l s] r]].
  destruct q,s; cbn [next RI.step_c frozen464] in Hnone; try discriminate.
  split; apply RI.halted_halts; reflexivity.
Qed.

Theorem original464_572_halting_equivalence :
  RI.halts frozen464 RI.c0 <-> RI.halts frozen572 RI.c0.
Proof.
  pose proof (RI.halts_iff frozen464 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff frozen572 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen464 c c' /\ reachable c'
    | None => RI.halts frozen464 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen572 c c' /\ reachable c'
    | None => RI.halts frozen572 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj2 (macro_none c HP Hnext)). }
  assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
  specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.

Print Assumptions source_one_step.
Print Assumptions target_seven_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions original464_572_halting_equivalence.
