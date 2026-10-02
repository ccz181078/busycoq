From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv759808 Require Import Frozen759 Projection.
Close Scope sym_scope.
Open Scope nat_scope.
Definition diamond_start (l r : Stream sym92) := (D6,(l,S192,Cons S192 r)).
Definition diamond_end (l r : Stream sym92) := (C6,(Cons S092 l,S192,r)).
Theorem source_one_step l r :
 RI.step frozen759 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.
Theorem target_three_steps l r :
 RI.multistep frozen808 3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.
Theorem target_positive_diamond l r :
 RI.progress frozen808 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_progress with (n:=2). apply target_three_steps. Qed.
Theorem exact_positive_diamond l r :
 RI.progress frozen759 (diamond_start l r) (diamond_end l r) /\
 RI.progress frozen808 (diamond_start l r) (diamond_end l r).
Proof. split; [apply RI.progress_base,source_one_step|apply target_positive_diamond]. Qed.
Lemma common_step q l s r c' : (q <> D6 \/ s <> S192) ->
 RI.step frozen759 (q,(l,s,r)) c' -> RI.step frozen808 (q,(l,s,r)) c'.
Proof.
 intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
 destruct q,s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.
Theorem same_undefined_cell q s : frozen759 (q,s) = None <-> frozen808 (q,s) = None.
Proof. destruct q,s; cbn; split; intros H; congruence. Qed.
Definition reachable (c : state6 * RI.tape) := RI.evstep frozen759 RI.c0 c.
Definition next := RI.step_c frozen759.
Theorem macro_some c c' : reachable c -> next c = Some c' ->
 RI.progress frozen759 c c' /\ RI.progress frozen808 c c' /\ reachable c'.
Proof.
 intros HR Hnext. assert (HM : RI.step frozen759 c c').
 { apply RI.step_c_spec. exact Hnext. }
 assert (HN : RI.progress frozen808 c c').
 { destruct c as [q [[l s] r]].
   destruct q,s; try (apply RI.progress_base; eapply common_step; [intuition discriminate|exact HM]).
   pose proof (frozen759_reachable_guard l r HR) as Hfirst.
   destruct r as [x rest]. cbn in Hfirst. subst x.
   cbn [next RI.step_c frozen759 RI.move_right] in Hnext. inversion Hnext; subst.
   exact (target_positive_diamond l rest). }
 split; [apply RI.progress_base; exact HM|]. split; [exact HN|].
 unfold reachable in *. eapply RI.evstep_trans; [exact HR|].
 apply RI.progress_evstep,RI.progress_base. exact HM.
Qed.
Theorem macro_none c : reachable c -> next c = None ->
 RI.halts frozen759 c /\ RI.halts frozen808 c.
Proof.
 intros _ Hnone. destruct c as [q [[l s] r]].
 destruct q,s; cbn [next RI.step_c frozen759] in Hnone; try discriminate.
 split; apply RI.halted_halts; reflexivity.
Qed.
Theorem original759_808_halting_equivalence :
 RI.halts frozen759 RI.c0 <-> RI.halts frozen808 RI.c0.
Proof.
 pose proof (RI.halts_iff frozen759 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
 pose proof (RI.halts_iff frozen808 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
 assert (Hsource : forall c, reachable c ->
   match next c with Some c' => RI.progress frozen759 c c' /\ reachable c'
   | None => RI.halts frozen759 c end).
 { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
   - pose proof (macro_some c c' HP Hnext). tauto.
   - exact (proj1 (macro_none c HP Hnext)). }
 assert (Htarget : forall c, reachable c ->
   match next c with Some c' => RI.progress frozen808 c c' /\ reachable c'
   | None => RI.halts frozen808 c end).
 { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
   - pose proof (macro_some c c' HP Hnext). tauto.
   - exact (proj2 (macro_none c HP Hnext)). }
 assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
 specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.
Print Assumptions source_one_step.
Print Assumptions target_three_steps.
Print Assumptions target_positive_diamond.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions original759_808_halting_equivalence.
