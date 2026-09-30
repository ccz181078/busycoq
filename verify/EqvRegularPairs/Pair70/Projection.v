(* One-bit observation for the already checked, halt-tolerant source invariant. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair70 Require Import Frozen70.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition bit_label (p : nat) : sym92 :=
  match p with
  | 0 => S092 | 1 => S192 | 2 => S092 | 3 => S192
  | 4 => S092 | 5 => S192 | 6 => S092 | 7 => S192
  | 8 => S092 | 9 => S192 | 10 => S192 | 11 => S092
  | 12 => S192 | 13 => S192 | 14 => S192 | 15 => S092
  | 16 => S192 | _ => S092
  end.

Example frozen70_projection_check : projection_check 17 frozen70_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen70_side_projection xs :
  bit_label (classify frozen70_delta xs) = Streams.hd (finite_side xs).
Proof.
  apply (finite_side_projection 17).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen70_check)).
  - exact frozen70_projection_check.
Qed.

(* Class zero has one incoming edge: zero from zero. *)
Definition zero_class_check n (d : DFA) : bool :=
  forallb (fun p => forallb (fun b =>
    negb (Nat.eqb (d p b) 0) ||
    (Nat.eqb p 0 && SourceCtx.sym_eqb b S092)) alphabet) (seq 0 n).
Theorem zero_class_check_true n d : zero_class_check n d = true ->
  forall p b, p < n -> d p b = 0 -> p = 0 /\ b = S092.
Proof.
  unfold zero_class_check. rewrite forall_states_true.
  intros HC p b Hp Hzero. specialize (HC p Hp).
  apply forall_symbols_true with (b:=b) in HC. rewrite Hzero in HC. cbn in HC.
  apply andb_true_iff in HC. destruct HC as [Hp0 Hb0].
  split; [now apply Nat.eqb_eq | now apply sym_eqb_true].
Qed.
Theorem classify_zero_blank n d : dfa_ok n d ->
  zero_class_check n d = true -> forall xs,
  classify d xs = 0 -> finite_side xs = const S092.
Proof.
  intros HD HZ xs. induction xs as [|b tail IH]; intro HC.
  - reflexivity.
  - cbn [classify] in HC.
    pose proof (zero_class_check_true n d HZ (classify d tail) b
      (classify_bound n d HD tail) HC) as [Ht Hb]. subst b.
    cbn [finite_side]. rewrite (IH Ht). symmetry. apply const_unfold.
Qed.
Example frozen70_zero_class_check : zero_class_check 17 frozen70_delta = true.
Proof. vm_compute. reflexivity. Qed.
Theorem frozen70_zero_is_blank xs : classify frozen70_delta xs = 0 ->
  finite_side xs = const S092.
Proof.
  apply (classify_zero_blank 17).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen70_check)).
  - exact frozen70_zero_class_check.
Qed.

Definition b0_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | B6, S092 => SourceCtx.sym_eqb (bit_label (leftD a)) S192 ||
      (Nat.eqb (leftD a) 0 && SourceCtx.sym_eqb (bit_label (rightD a)) S092)
  | _,_ => true
  end.
Example frozen70_guard_check : forallb b0_guard_check frozen70_invariant = true.
Proof. vm_compute. reflexivity. Qed.
Theorem frozen70_abstract_guard l r :
  In (E B6 S092 l r) frozen70_invariant ->
  bit_label l = S192 \/ (l = 0 /\ bit_label r = S092).
Proof.
  intro H. pose proof frozen70_guard_check as HC.
  apply forallb_forall with (x:=E B6 S092 l r) in HC; [|exact H].
  cbn [b0_guard_check] in HC. apply orb_true_iff in HC.
  destruct HC as [HL|H0].
  - left. now apply sym_eqb_true.
  - right. apply andb_true_iff in H0. destruct H0 as [H0 HR].
    split; [now apply Nat.eqb_eq | now apply sym_eqb_true].
Qed.
Theorem frozen70_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen70 RI.c0 (B6,(l,S092,r)) ->
  Streams.hd l = S192 \/ (l = const S092 /\ Streams.hd r = S092).
Proof.
  intro H. apply frozen70_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  apply frozen70_abstract_guard in Hin. destruct Hin as [HL|[HZ HR]].
  - left. rewrite <- frozen70_side_projection. exact HL.
  - right. split.
    + now apply frozen70_zero_is_blank.
    + rewrite <- frozen70_side_projection. exact HR.
Qed.
Print Assumptions frozen70_side_projection.
Print Assumptions zero_class_check_true.
Print Assumptions classify_zero_blank.
Print Assumptions frozen70_zero_is_blank.
Print Assumptions frozen70_abstract_guard.
Print Assumptions frozen70_reachable_guard.

(* Complete assumption inventory for this unit. *)
Print Assumptions sym_eqb_true.
Print Assumptions frozen70_projection_check.
Print Assumptions frozen70_zero_class_check.
Print Assumptions frozen70_guard_check.
