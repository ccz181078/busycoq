From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat Lia.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv759808 Require Import Frozen759.
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
| 16 => S192
| 17 => S092
| 18 => S192
| 19 => S192
| 20 => S092
| 21 => S192
| 22 => S092
| 23 => S192
| 24 => S192
| 25 => S092
| 26 => S192
| 27 => S092
| 28 => S192
| 29 => S092
| 30 => S192
| 31 => S092
| 32 => S192
| 33 => S092
| 34 => S192
| 35 => S092
| 36 => S192
| 37 => S192
| 38 => S092
| 39 => S192
| 40 => S092
| 41 => S092
| 42 => S092
| 43 => S192
| 44 => S092
| 45 => S192
| 46 => S092
| 47 => S192
| 48 => S092
| 49 => S192
| 50 => S192
| 51 => S092
| 52 => S192
| 53 => S092
| 54 => S192
| 55 => S092
| 56 => S192
| 57 => S092
| 58 => S192
| 59 => S092
| 60 => S192
| 61 => S092
| 62 => S192
| 63 => S092
| 64 => S192
| 65 => S192
| 66 => S092
| 67 => S192
| 68 => S092
| 69 => S192
| 70 => S192
| 71 => S092
| 72 => S192
| 73 => S092
| 74 => S192
| 75 => S092
| 76 => S192
| 77 => S092
| 78 => S092
| 79 => S192
| 80 => S092
| 81 => S192
| 82 => S092
| 83 => S192
| 84 => S192
| 85 => S092
| 86 => S192
| 87 => S092
| 88 => S092
| 89 => S092
| 90 => S192
| 91 => S092
| 92 => S192
| 93 => S092
| 94 => S192
| 95 => S092
| 96 => S192
| 97 => S092
| 98 => S192
| 99 => S092
| 100 => S092
| 101 => S192
| 102 => S092
| 103 => S192
| 104 => S192
| 105 => S092
| 106 => S192
| 107 => S092
| 108 => S192
| 109 => S092
| 110 => S092
| 111 => S192
| 112 => S092
| 113 => S092
| 114 => S192
| 115 => S092
| 116 => S192
| 117 => S092
| 118 => S192
| 119 => S092
| 120 => S092
| 121 => S092
| 122 => S192
| 123 => S092
| 124 => S192
| 125 => S092
| 126 => S192
| 127 => S192
| 128 => S092
| 129 => S192
| 130 => S092
| 131 => S092
| 132 => S192
| 133 => S092
| _ => S092 end.

Lemma frozen759_dfa_ok : dfa_ok 134 frozen759_delta.
Proof. exact (proj1 (proj1 (check_true _ _ _ _) frozen759_check)). Qed.
Lemma head_label_zero : head_label 0 = S092.
Proof. reflexivity. Qed.
Lemma head_label_push p b : p < 134 -> head_label (frozen759_delta p b) = b.
Proof. intros Hp. do 134 (destruct p as [|p]; [destruct b; reflexivity |]). lia. Qed.
Theorem side_head_projection xs : head_label (classify frozen759_delta xs) = Streams.hd (finite_side xs).
Proof.
 induction xs as [|b xs IH]; cbn [classify finite_side].
 - reflexivity.
 - rewrite head_label_push; [reflexivity|].
   apply classify_bound with (n:=134), frozen759_dfa_ok.
Qed.
Lemma sym_eqb_true a b : SourceCtx.sym_eqb a b = true <-> a = b.
Proof. destruct (SourceCtx.sym_eqb_spec a b); intuition discriminate. Qed.
Definition d1_guard_check (a : entry) : bool := match control a, scanned a with
 | D6,S192 => SourceCtx.sym_eqb (head_label (rightD a)) S192
 | _,_ => true end.
Example frozen759_guard_check : forallb d1_guard_check frozen759_invariant = true.
Proof. vm_compute. reflexivity. Qed.
Lemma frozen759_abstract_guard l r : In (E D6 S192 l r) frozen759_invariant -> head_label r = S192.
Proof.
 intros Hin. pose proof frozen759_guard_check as HC.
 apply forallb_forall with (x:=E D6 S192 l r) in HC; [|exact Hin].
 cbn [d1_guard_check] in HC. now apply sym_eqb_true in HC.
Qed.
Theorem frozen759_reachable_guard (l r : Stream sym92) :
 RI.evstep frozen759 RI.c0 (D6,(l,S192,r)) -> Streams.hd r = S192.
Proof.
 intros H. apply frozen759_reachable_invariant in H.
 destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
 apply frozen759_abstract_guard in Hin. now rewrite side_head_projection in Hin.
Qed.
Print Assumptions frozen759_dfa_ok.
Print Assumptions head_label_push.
Print Assumptions side_head_projection.
Print Assumptions frozen759_guard_check.
Print Assumptions frozen759_abstract_guard.
Print Assumptions frozen759_reachable_guard.
