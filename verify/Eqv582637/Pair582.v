From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv582637 Require Import Frozen582 Projection.
Close Scope sym_scope.
Open Scope nat_scope.
Definition diamond_start (l r : Stream sym92) := (F6,(Cons S092 l,S192,r)).
Definition diamond_end (l r : Stream sym92) := (A6,(l,S092,Cons S092 r)).
Theorem source_three_steps l r :
 RI.multistep frozen582 3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem source_positive_diamond l r :
 RI.progress frozen582 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_progress with (n:=2). apply source_three_steps. Qed.
Theorem target_one_step l r :
 RI.step frozen637 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem exact_positive_diamond l r :
 RI.progress frozen582 (diamond_start l r) (diamond_end l r) /\
 RI.progress frozen637 (diamond_start l r) (diamond_end l r).
Proof. split; [apply source_positive_diamond|apply RI.progress_base,target_one_step]. Qed.
Lemma common_step q l s r c' : (q <> F6 \/ s <> S192) ->
 RI.step frozen637 (q,(l,s,r)) c' -> RI.step frozen582 (q,(l,s,r)) c'.
Proof.
 intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
 destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.
Theorem same_undefined_cell q s : frozen582 (q,s) = None <-> frozen637 (q,s) = None.
Proof. destruct q,s; cbn; split; intros H; congruence. Qed.
Definition reachable (c : state6 * RI.tape) := RI.evstep frozen582 RI.c0 c.
Definition next := RI.step_c frozen637.
Theorem macro_some c c' : reachable c -> next c = Some c' ->
 RI.progress frozen582 c c' /\ RI.progress frozen637 c c' /\ reachable c'.
Proof.
 intros HR Hnext. assert (HM : RI.step frozen637 c c').
 { apply RI.step_c_spec. exact Hnext. }
 assert (HN : RI.progress frozen582 c c').
 { destruct c as [q [[l s] r]].
   destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate|exact HM]).
   pose proof (frozen582_reachable_guard l r HR) as Hfirst.
   destruct l as [x rest]. cbn in Hfirst. subst x.
   cbn [next RI.step_c frozen637 RI.move_left] in Hnext. inversion Hnext; subst.
   exact (source_positive_diamond rest r). }
 split; [exact HN|]. split; [apply RI.progress_base; exact HM|].
 unfold reachable in *. eapply RI.evstep_trans; [exact HR|].
 apply RI.progress_evstep. exact HN.
Qed.
Theorem macro_none c : reachable c -> next c = None ->
 RI.halts frozen582 c /\ RI.halts frozen637 c.
Proof.
 intros _ Hnone. destruct c as [q [[l s] r]].
 destruct q,s; cbn [next RI.step_c frozen637] in Hnone; try discriminate.
 split; apply RI.halted_halts; reflexivity.
Qed.
Theorem original582_637_halting_equivalence :
 RI.halts frozen582 RI.c0 <-> RI.halts frozen637 RI.c0.
Proof.
 pose proof (RI.halts_iff frozen582 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
 pose proof (RI.halts_iff frozen637 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
 assert (Hsource : forall c, reachable c ->
   match next c with Some c' => RI.progress frozen582 c c' /\ reachable c'
   | None => RI.halts frozen582 c end).
 { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
   - pose proof (macro_some c c' HP Hnext). tauto.
   - exact (proj1 (macro_none c HP Hnext)). }
 assert (Htarget : forall c, reachable c ->
   match next c with Some c' => RI.progress frozen637 c c' /\ reachable c'
   | None => RI.halts frozen637 c end).
 { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
   - pose proof (macro_some c c' HP Hnext). tauto.
   - exact (proj2 (macro_none c HP Hnext)). }
 assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
 specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.
Print Assumptions source_three_steps.
Print Assumptions source_positive_diamond.
Print Assumptions target_one_step.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions original582_637_halting_equivalence.
