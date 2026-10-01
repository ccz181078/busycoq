(* One-bit observation for the already checked, halt-tolerant source invariant. *)
From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat.
From BusyCoq Require Import TM.
From BusyCoq Require Import RegularInvariant62.
From BusyCoq.Eqv326408 Require Import Frozen408.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Definition bit_label (p : nat) : sym92 :=
 match p with
| 0 => S092
| 1 => S192
| 2 => S092
| 3 => S192
| 4 => S092
| 5 => S192
| 6 => S092
| 7 => S192
| 8 => S092
| 9 => S192
| 10 => S092
| 11 => S192
| 12 => S092
| 13 => S192
| 14 => S092
| 15 => S192
| 16 => S092
| 17 => S192
| 18 => S092
| 19 => S192
| 20 => S092
| 21 => S192
| 22 => S092
| 23 => S192
| 24 => S092
| 25 => S192
| 26 => S092
| 27 => S192
| 28 => S092
| 29 => S192
| 30 => S092
| 31 => S192
| 32 => S092
| 33 => S192
| 34 => S092
| 35 => S192
| 36 => S092
| 37 => S192
| 38 => S092
| 39 => S192
| 40 => S092
| 41 => S192
| 42 => S092
| 43 => S192
| 44 => S192
| 45 => S192
| 46 => S192
| _ => S092
end.

Definition projection_check n (d : DFA) (label : nat -> sym92) : bool :=
  SourceCtx.sym_eqb (label 0) S092 &&
  forallb (fun p => forallb (fun b =>
    SourceCtx.sym_eqb (label (d p b)) b) alphabet) (seq 0 n).

Lemma sym_eqb_true a b : SourceCtx.sym_eqb a b = true <-> a = b.
Proof. destruct (SourceCtx.sym_eqb_spec a b); intuition discriminate. Qed.

Lemma projection_check_true n d label : projection_check n d label = true <->
  label 0 = S092 /\ forall p b, p < n -> label (d p b) = b.
Proof.
  unfold projection_check. rewrite andb_true_iff, sym_eqb_true, forall_states_true.
  split.
  - intros [H0 H]. split; [exact H0 |]. intros p b Hp.
    specialize (H p Hp). apply forall_symbols_true with (b:=b) in H.
    now apply sym_eqb_true.
  - intros [H0 H]. split; [exact H0 |]. intros p Hp.
    apply forall_symbols_true. intros b. apply sym_eqb_true, H, Hp.
Qed.

Theorem finite_side_projection n d label : dfa_ok n d ->
  projection_check n d label = true -> forall xs,
  label (classify d xs) = Streams.hd (finite_side xs).
Proof.
  intros HD HP xs. apply projection_check_true in HP.
  destruct HP as [H0 H]. destruct xs as [|b tail]; cbn.
  - exact H0.
  - apply H. apply classify_bound with (n:=n), HD.
Qed.

Example frozen408_projection_check : projection_check 47 frozen408_delta bit_label = true.
Proof. vm_compute. reflexivity. Qed.

Theorem frozen408_side_projection xs :
  bit_label (classify frozen408_delta xs) = Streams.hd (finite_side xs).
Proof.
  apply (finite_side_projection 47).
  - exact (proj1 (proj1 (check_true _ _ _ _) frozen408_check)).
  - exact frozen408_projection_check.
Qed.

Definition a0_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | A6, S092 => SourceCtx.sym_eqb (bit_label (rightD a)) S092
  | _, _ => true
  end.

Example frozen408_guard_check : forallb a0_guard_check frozen408_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frozen408_abstract_guard l r :
  In (E A6 S092 l r) frozen408_invariant -> bit_label r = S092.
Proof.
  intros H. pose proof frozen408_guard_check as HC.
  apply forallb_forall with (x:=E A6 S092 l r) in HC; [|exact H].
  cbn [a0_guard_check] in HC. now apply sym_eqb_true.
Qed.

Theorem frozen408_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen408 RI.c0 (A6, (l, S092, r)) -> Streams.hd r = S092.
Proof.
  intros H. apply frozen408_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  rewrite <- frozen408_side_projection. now apply frozen408_abstract_guard in Hin.
Qed.

Print Assumptions projection_check_true.
Print Assumptions finite_side_projection.
Print Assumptions frozen408_side_projection.
Print Assumptions frozen408_abstract_guard.
Print Assumptions frozen408_reachable_guard.
