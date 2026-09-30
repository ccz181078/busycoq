(* One-bit observation for the already checked, halt-tolerant source invariant. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv220723 Require Import Projection.
From BusyCoq.EqvRegularPairs.Pair439 Require Import Frozen439.
Close Scope sym_scope.
Open Scope nat_scope.
Import ListNotations.

Definition bit_label (p : nat) : sym92 :=
  match p with
  | 0 => S092 | 1 => S192 | 2 => S092 | 3 => S192
  | 4 => S092 | 5 => S192 | 6 => S192 | 7 => S192
  | 8 => S092 | 9 => S192 | _ => S092
  end.

Example frozen439_projection_check : projection_check 10 frozen439_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen439_side_projection xs :
  bit_label (classify frozen439_delta xs) = Streams.hd (finite_side xs).
Proof.
  apply (finite_side_projection 10).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen439_check)).
  - exact frozen439_projection_check.
Qed.

Definition b0_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | B6, S092 => SourceCtx.sym_eqb (bit_label (rightD a)) S092
  | _, _ => true
  end.

Example frozen439_guard_check : forallb b0_guard_check frozen439_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frozen439_abstract_guard l r :
  In (E B6 S092 l r) frozen439_invariant -> bit_label r = S092.
Proof.
  intros H. pose proof frozen439_guard_check as HC.
  apply forallb_forall with (x:=E B6 S092 l r) in HC; [|exact H].
  cbn [b0_guard_check] in HC. now apply sym_eqb_true.
Qed.

Theorem frozen439_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen439 RI.c0 (B6, (l, S092, r)) -> Streams.hd r = S092.
Proof.
  intros H. apply frozen439_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  rewrite <- frozen439_side_projection. now apply frozen439_abstract_guard in Hin.
Qed.

Print Assumptions frozen439_side_projection.
Print Assumptions frozen439_abstract_guard.
Print Assumptions frozen439_reachable_guard.
