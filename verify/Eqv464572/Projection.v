From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.PeanoNat Lia.
From BusyCoq Require Import TM RegularInvariant62.
From BusyCoq.Eqv464572 Require Import Frozen464Indexed.
Import ListNotations.
Close Scope sym_scope.
Open Scope nat_scope.

Definition pair_label (p : nat) : sym92 * sym92 :=
  match p with
  | 0 => (S092, S092)
  | 1 => (S192, S092)
  | 2 => (S092, S192)
  | 3 => (S192, S192)
  | 4 => (S092, S092)
  | 5 => (S192, S092)
  | 6 => (S092, S192)
  | 7 => (S192, S192)
  | 8 => (S092, S092)
  | 9 => (S092, S192)
  | 10 => (S192, S192)
  | 11 => (S092, S092)
  | 12 => (S192, S092)
  | 13 => (S092, S192)
  | 14 => (S192, S192)
  | 15 => (S092, S092)
  | 16 => (S192, S092)
  | 17 => (S092, S192)
  | 18 => (S092, S092)
  | 19 => (S192, S092)
  | 20 => (S092, S092)
  | 21 => (S192, S092)
  | 22 => (S092, S192)
  | 23 => (S092, S192)
  | 24 => (S092, S092)
  | 25 => (S192, S092)
  | 26 => (S092, S192)
  | 27 => (S192, S092)
  | 28 => (S092, S192)
  | 29 => (S192, S192)
  | 30 => (S192, S092)
  | 31 => (S092, S092)
  | 32 => (S092, S092)
  | 33 => (S192, S092)
  | 34 => (S092, S192)
  | 35 => (S192, S092)
  | 36 => (S092, S192)
  | 37 => (S192, S192)
  | 38 => (S092, S092)
  | 39 => (S092, S092)
  | 40 => (S192, S192)
  | 41 => (S092, S092)
  | 42 => (S092, S092)
  | 43 => (S092, S092)
  | 44 => (S092, S192)
  | 45 => (S092, S092)
  | 46 => (S092, S092)
  | 47 => (S092, S092)
  | 48 => (S192, S092)
  | _ => (S092,S092)
  end.

Lemma frozen464_dfa_ok : dfa_ok 49 frozen464_delta.
Proof. exact (proj1 (proj1 (check_true _ _ _ _) frozen464_check)). Qed.

Lemma pair_label_zero : pair_label 0 = (S092,S092).
Proof. reflexivity. Qed.

Lemma pair_label_push p b : p < 49 ->
  pair_label (frozen464_delta p b) = (b, fst (pair_label p)).
Proof.
  intros Hp.
  do 49 (destruct p as [|p]; [destruct b; reflexivity |]).
  lia.
Qed.

Theorem pair_side_projection xs :
  pair_label (classify frozen464_delta xs) =
  (Streams.hd (finite_side xs), Streams.hd (Streams.tl (finite_side xs))).
Proof.
  induction xs as [|b xs IH]; cbn [classify finite_side].
  - reflexivity.
  - rewrite pair_label_push.
    + rewrite IH. reflexivity.
    + apply classify_bound with (n:=49), frozen464_dfa_ok.
Qed.

Lemma sym_eqb_true a b : SourceCtx.sym_eqb a b = true <-> a = b.
Proof. destruct (SourceCtx.sym_eqb_spec a b); intuition discriminate. Qed.

Definition f1_guard_check (a : entry) : bool :=
  match control a, scanned a with
  | F6, S192 => SourceCtx.sym_eqb (fst (pair_label (leftD a))) S092 &&
                SourceCtx.sym_eqb (snd (pair_label (leftD a))) S192
  | _, _ => true
  end.

Example frozen464_guard_check : forallb f1_guard_check frozen464_invariant = true.
Proof. vm_compute. reflexivity. Qed.

Lemma frozen464_abstract_guard l r :
  In (E F6 S192 l r) frozen464_invariant -> pair_label l = (S092,S192).
Proof.
  intros Hin. pose proof frozen464_guard_check as HC.
  apply forallb_forall with (x:=E F6 S192 l r) in HC; [|exact Hin].
  cbn [f1_guard_check] in HC.
  apply andb_true_iff in HC. destruct HC as [Ha Hb].
  apply sym_eqb_true in Ha. apply sym_eqb_true in Hb.
  change (fst (pair_label l) = S092) in Ha.
  change (snd (pair_label l) = S192) in Hb.
  destruct (pair_label l) as [a b]. cbn in Ha,Hb. now subst.
Qed.

Theorem frozen464_reachable_guard (l r : Stream sym92) :
  RI.evstep frozen464 RI.c0 (F6,(l,S192,r)) ->
  Streams.hd l = S092 /\ Streams.hd (Streams.tl l) = S192.
Proof.
  intros H. apply frozen464_reachable_invariant in H.
  destruct H as [q [s [ls [rs [Heq Hin]]]]]. inversion Heq; subst.
  apply frozen464_abstract_guard in Hin. rewrite pair_side_projection in Hin.
  inversion Hin. auto.
Qed.

Print Assumptions frozen464_dfa_ok.
Print Assumptions pair_label_push.
Print Assumptions pair_side_projection.
Print Assumptions frozen464_abstract_guard.
Print Assumptions frozen464_reachable_guard.
