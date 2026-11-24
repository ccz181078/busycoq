(** The map on visits A(a, b) of 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC (the wiki's rules, analysis by
    Racheline), and its iterates. [None] is the halt. *)
From Coq Require Import PeanoNat.
Import Nat.

Definition op (x : nat * nat) : option (nat * nat) :=
  let (a, b) := x in
  if b =? 3 then None
  else if b =? 2 then Some (a - 3, 7)
  else if b <=? a then Some (a - b + 1, 2 * b + 3)
  else if b =? a + 1 then Some (4, 2 * a + 4)
  else if b =? a + 2 then Some (1, 2 * a + 7)
  else if even a then Some (2 * a + 4, b - a - 1)
  else if b =? a + 3 then Some (2 * a + 1, 9)
  else Some (2 * a + 3, b - a).

Fixpoint opIter (k : nat) (x : nat * nat) : option (nat * nat) :=
  match k with
  | O => Some x
  | S k => match op x with Some y => opIter k y | None => None end
  end.

Lemma opIter_add m n x : opIter (m + n) x = match opIter m x with Some y => opIter n y | None => None end.
Proof.
  revert x. induction m as [|m IH]; intros x; [reflexivity|]. cbn. destruct (op x); [apply IH|reflexivity].
Qed.
