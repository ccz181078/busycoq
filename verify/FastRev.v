From Coq Require Import List.

Import ListNotations.
Set Implicit Arguments.

(** A tail-recursive list reversal for executable developments.

    Coq 8.20's [List.rev] is specified by [rev xs ++ [x]] in the recursive
    branch, so reducing it on a list of length [n] takes quadratic time.
    The accumulator below visits every cons cell exactly once.  The lemmas
    relate the executable operation to the standard-library specification;
    clients can therefore keep using the usual [List.rev] theory in proofs. *)
Fixpoint fast_rev_append {A : Type} (xs acc : list A) : list A :=
  match xs with
  | [] => acc
  | x :: xs' => fast_rev_append xs' (x :: acc)
  end.

Definition fast_rev {A : Type} (xs : list A) : list A :=
  fast_rev_append xs [].

Lemma fast_rev_append_spec {A : Type} (xs acc : list A) :
  fast_rev_append xs acc = List.rev xs ++ acc.
Proof.
  revert acc. induction xs as [|x xs IH]; intros acc; cbn [fast_rev_append].
  - reflexivity.
  - rewrite IH. cbn [List.rev]. rewrite <-app_assoc. reflexivity.
Qed.

Lemma fast_rev_spec {A : Type} (xs : list A) :
  fast_rev xs = List.rev xs.
Proof.
  unfold fast_rev. rewrite fast_rev_append_spec,app_nil_r. reflexivity.
Qed.

Lemma fast_rev_nil {A : Type} : @fast_rev A [] = [].
Proof. reflexivity. Qed.

Lemma fast_rev_cons {A : Type} (x : A) (xs : list A) :
  fast_rev (x :: xs) = fast_rev xs ++ [x].
Proof. repeat rewrite fast_rev_spec. reflexivity. Qed.

Lemma fast_rev_app_distr {A : Type} (xs ys : list A) :
  fast_rev (xs ++ ys) = fast_rev ys ++ fast_rev xs.
Proof. repeat rewrite fast_rev_spec. apply List.rev_app_distr. Qed.

Lemma fast_rev_involutive {A : Type} (xs : list A) :
  fast_rev (fast_rev xs) = xs.
Proof. repeat rewrite fast_rev_spec. apply List.rev_involutive. Qed.

Arguments fast_rev_append {A} xs acc.
Arguments fast_rev {A} xs.
