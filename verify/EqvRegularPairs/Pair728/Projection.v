(* One-bit observation for the already checked, halt-tolerant source invariant. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair728 Require Import Frozen728.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition bit_label (p : nat) : sym92 :=
  match p with
  | 0 => S092 | 1 => S192 | 2 => S092 | 3 => S192
  | 4 => S092 | 5 => S192 | 6 => S192 | 7 => S192
  | 8 => S092 | 9 => S192 | _ => S092
  end.

Example frozen728_projection_check : projection_check 10 frozen728_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen728_side_projection xs :
  bit_label (classify frozen728_delta xs) = Streams.hd (finite_side xs).
Proof.
  apply (finite_side_projection 10).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen728_check)).
  - exact frozen728_projection_check.
Qed.

Definition b0_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | B6, S092 => Nat.eqb (rightD a) 0
  | _, _ => true
  end.

Example frozen728_guard_check : forallb b0_guard_check frozen728_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frozen728_abstract_guard l r :
  In (E B6 S092 l r) frozen728_invariant -> r = 0.
Proof.
  intros H. pose proof frozen728_guard_check as HC.
  apply forallb_forall with (x:=E B6 S092 l r) in HC; [|exact H].
  cbn [b0_guard_check] in HC. now apply Nat.eqb_eq.
Qed.

Theorem frozen728_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen728 RI.c0 (B6, (l, S092, r)) -> Streams.hd r = S092.
Proof.
  intros H. apply frozen728_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  rewrite <- frozen728_side_projection. apply frozen728_abstract_guard in Hin.
  rewrite Hin. reflexivity.
Qed.

Print Assumptions sym_eqb_true.
Print Assumptions frozen728_projection_check.
Print Assumptions frozen728_side_projection.
Print Assumptions frozen728_guard_check.
Print Assumptions frozen728_abstract_guard.
Print Assumptions frozen728_reachable_guard.
