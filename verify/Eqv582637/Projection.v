From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat Lia.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv582637 Require Import Frozen582.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.
Definition head_label (p : nat) : sym92 := match p with
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
| 31 => S092
| 32 => S192
| 33 => S092
| 34 => S192
| 35 => S092
| 36 => S192
| 37 => S092
| 38 => S192
| 39 => S092
| 40 => S192
| 41 => S092
| 42 => S192
| 43 => S092
| 44 => S192
| 45 => S092
| 46 => S192
| 47 => S092
| 48 => S192
| 49 => S092
| 50 => S192
| 51 => S092
| 52 => S092
| 53 => S092
| 54 => S192
| 55 => S092
| 56 => S092
| 57 => S192
| 58 => S092
| 59 => S192
| 60 => S192
| 61 => S092
| 62 => S092
| 63 => S192
| 64 => S092
| 65 => S092
| 66 => S192
| 67 => S092
| 68 => S192
| 69 => S092
| 70 => S192
| 71 => S092
| 72 => S192
| 73 => S192
| _ => S092 end.

Lemma frozen582_dfa_ok : dfa_ok 74 frozen582_delta.
Proof. exact (proj1 (proj1 (check_true _ _ _ _) frozen582_check)). Qed.
Lemma head_label_zero : head_label 0 = S092.
Proof. reflexivity. Qed.
Lemma head_label_push p b : p < 74 -> head_label (frozen582_delta p b) = b.
Proof. intros Hp. do 74 (destruct p as [|p]; [destruct b; reflexivity |]). lia. Qed.
Theorem side_head_projection xs : head_label (classify frozen582_delta xs) = Streams.hd (finite_side xs).
Proof.
 induction xs as [|b xs IH]; cbn [classify finite_side].
 - reflexivity.
 - rewrite head_label_push; [reflexivity|].
   apply classify_bound with (n:=74), frozen582_dfa_ok.
Qed.
Lemma sym_eqb_true a b : SourceCtx.sym_eqb a b = true <-> a = b.
Proof. destruct (SourceCtx.sym_eqb_spec a b); intuition discriminate. Qed.
Definition f1_guard_check (a : entry) : bool := match control a, scanned a with
 | F6,S192 => SourceCtx.sym_eqb (head_label (leftD a)) S092
 | _,_ => true end.
Example frozen582_guard_check : forallb f1_guard_check frozen582_invariant = true.
Proof. vm_compute. reflexivity. Qed.
Lemma frozen582_abstract_guard l r : In (E F6 S192 l r) frozen582_invariant -> head_label l = S092.
Proof.
 intros Hin. pose proof frozen582_guard_check as HC.
 apply forallb_forall with (x:=E F6 S192 l r) in HC; [|exact Hin].
 cbn [f1_guard_check] in HC. now apply sym_eqb_true in HC.
Qed.
Theorem frozen582_reachable_guard (l r : Stream sym92) :
 RI.evstep frozen582 RI.c0 (F6,(l,S192,r)) -> Streams.hd l = S092.
Proof.
 intros H. apply frozen582_reachable_invariant in H.
 destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
 apply frozen582_abstract_guard in Hin. now rewrite side_head_projection in Hin.
Qed.
Print Assumptions frozen582_dfa_ok.
Print Assumptions head_label_push.
Print Assumptions side_head_projection.
Print Assumptions frozen582_guard_check.
Print Assumptions frozen582_abstract_guard.
Print Assumptions frozen582_reachable_guard.
