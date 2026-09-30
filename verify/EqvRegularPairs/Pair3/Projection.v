(* One-bit observation for the already checked, halt-tolerant source invariant. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair3 Require Import Frozen3.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition bit_label (p : nat) : sym92 :=
  match p with
  | 0 => S092 | 1 => S192 | 2 => S092 | 3 => S192
  | 4 => S092 | 5 => S192 | 6 => S192 | 7 => S192
  | 8 => S092 | 9 => S192 | _ => S092
  end.

Example frozen3_projection_check : projection_check 10 frozen3_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen3_side_projection xs :
  bit_label (classify frozen3_delta xs) = Streams.hd (finite_side xs).
Proof.
  apply (finite_side_projection 10).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen3_check)).
  - exact frozen3_projection_check.
Qed.

Definition d0_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | D6, S092 => SourceCtx.sym_eqb (bit_label (leftD a)) S092
  | _, _ => true
  end.

Example frozen3_guard_check : forallb d0_guard_check frozen3_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frozen3_abstract_guard l r :
  In (E D6 S092 l r) frozen3_invariant -> bit_label l = S092.
Proof.
  intros H. pose proof frozen3_guard_check as HC.
  apply forallb_forall with (x:=E D6 S092 l r) in HC; [|exact H].
  cbn [d0_guard_check] in HC. now apply sym_eqb_true.
Qed.

Theorem frozen3_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen3 RI.c0 (D6, (l, S092, r)) -> Streams.hd l = S092.
Proof.
  intros H. apply frozen3_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  rewrite <- frozen3_side_projection. now apply frozen3_abstract_guard in Hin.
Qed.

Print Assumptions frozen3_side_projection.
Print Assumptions frozen3_abstract_guard.
Print Assumptions frozen3_reachable_guard.
