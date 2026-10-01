(* Exact original frozen815 rows 220/723, without relabeling or reflection. *)
From Coq Require Import Lists.Streams String.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Frozen220 EndpointEncoding.
From BusyCoq.Eqv220723 Require Import Projection.
Close Scope sym_scope.
Open Scope nat_scope.

Definition frozen723 : RI.TM := fun qs => match qs with
| (A6, S092) => Some (S192, R, B6)
| (A6, S192) => Some (S192, R, E6)
| (B6, S092) => Some (S092, L, C6)
| (B6, S192) => Some (S192, R, F6)
| (C6, S092) => None
| (C6, S192) => Some (S192, L, D6)
| (D6, S092) => Some (S192, L, E6)
| (D6, S192) => Some (S092, L, D6)
| (E6, S092) => Some (S192, L, A6)
| (E6, S192) => Some (S192, L, B6)
| (F6, S092) => Some (S192, R, F6)
| (F6, S192) => Some (S092, R, A6)
end.

Theorem source220_literal_binding : machine_string frozen220 =
  "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RE0RA"%string.
Proof. exact frozen220_literal_binding. Qed.
Theorem target723_literal_binding : machine_string frozen723 =
  "1RB1RE_0LC1RF_---1LD_1LE0LD_1LA1LB_1RF0RA"%string.
Proof. reflexivity. Qed.

Definition diamond_start (l r : Stream sym92) := (F6, (l, S092, Cons S192 r)).
Definition diamond_end (l r : Stream sym92) := (F6, (Cons S192 l, S192, r)).

Theorem source_three_steps l r :
  RI.multistep frozen220 3 (diamond_start l r) (diamond_end l r).
Proof. apply RI.multistep_c_spec. reflexivity. Qed.

Theorem target_one_step l r :
  RI.step frozen723 (diamond_start l r) (diamond_end l r).
Proof. apply RI.step_c_spec. reflexivity. Qed.

Theorem source_positive_diamond l r :
  RI.progress frozen220 (diamond_start l r) (diamond_end l r).
Proof.
  apply RI.multistep_progress with (n:=2). exact (source_three_steps l r).
Qed.

Theorem exact_positive_diamond l r :
  RI.progress frozen220 (diamond_start l r) (diamond_end l r) /\
  RI.progress frozen723 (diamond_start l r) (diamond_end l r).
Proof. split; [apply source_positive_diamond | apply RI.progress_base, target_one_step]. Qed.

Lemma common_cell q s : (q <> F6 \/ s <> S092) -> frozen220 (q,s) = frozen723 (q,s).
Proof. destruct q, s; cbn; intuition congruence. Qed.

Lemma common_step q l s r c' : (q <> F6 \/ s <> S092) ->
  RI.step frozen723 (q,(l,s,r)) c' -> RI.step frozen220 (q,(l,s,r)) c'.
Proof.
  intros Hcell Hstep. apply RI.step_c_spec in Hstep. apply RI.step_c_spec.
  destruct q, s; try exact Hstep. exfalso. destruct Hcell; congruence.
Qed.

Theorem same_undefined_cell q s :
  frozen220 (q,s) = None <-> frozen723 (q,s) = None.
Proof. destruct q, s; cbn; split; intros H; congruence. Qed.

Definition reachable (c : state6 * RI.tape) := RI.evstep frozen220 RI.c0 c.
Definition next := RI.step_c frozen723.

Theorem macro_some c c' : reachable c -> next c = Some c' ->
  RI.progress frozen220 c c' /\ RI.progress frozen723 c c' /\ reachable c'.
Proof.
  intros HR Hnext. assert (HN : RI.step frozen723 c c').
  { apply RI.step_c_spec. exact Hnext. }
  assert (HM : RI.progress frozen220 c c').
  { destruct c as [q [[l s] r]].
    destruct q, s; try (apply RI.progress_base; eapply common_step; [intuition discriminate | exact HN]).
    pose proof (frozen220_reachable_guard l r HR) as Hguard.
    destruct r as [b tail]. cbn in Hguard. subst b.
    cbn [next RI.step_c frozen723 RI.move_right] in Hnext. inversion Hnext; subst.
    exact (source_positive_diamond l tail). }
  split; [exact HM |]. split; [apply RI.progress_base; exact HN |].
  unfold reachable in *. eapply RI.evstep_trans; [exact HR |].
  apply RI.progress_evstep. exact HM.
Qed.

Theorem macro_none c : reachable c -> next c = None ->
  RI.halts frozen220 c /\ RI.halts frozen723 c.
Proof.
  intros _ Hnone. destruct c as [q [[l s] r]].
  destruct q, s; cbn [next RI.step_c frozen723] in Hnone; try discriminate.
  split; apply RI.halted_halts; reflexivity.
Qed.

Theorem original220_723_halting_equivalence :
  RI.halts frozen220 RI.c0 <-> RI.halts frozen723 RI.c0.
Proof.
  pose proof (RI.halts_iff frozen220 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HL.
  pose proof (RI.halts_iff frozen723 (state6 * RI.tape) RI.c0 next (fun c => c) reachable) as HR.
  assert (Hsource : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen220 c c' /\ reachable c'
    | None => RI.halts frozen220 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj1 (macro_none c HP Hnext)). }
  assert (Htarget : forall c, reachable c ->
    match next c with Some c' => RI.progress frozen723 c c' /\ reachable c'
    | None => RI.halts frozen723 c end).
  { intros c HP. destruct (next c) as [c'|] eqn:Hnext.
    - pose proof (macro_some c c' HP Hnext). tauto.
    - exact (proj2 (macro_none c HP Hnext)). }
  assert (Hinitial : reachable RI.c0) by (unfold reachable; constructor).
  specialize (HL Hsource Hinitial). specialize (HR Htarget Hinitial). tauto.
Qed.

Print Assumptions source220_literal_binding.
Print Assumptions target723_literal_binding.
Print Assumptions source_three_steps.
Print Assumptions exact_positive_diamond.
Print Assumptions same_undefined_cell.
Print Assumptions macro_some.
Print Assumptions macro_none.
Print Assumptions original220_723_halting_equivalence.
